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
Require Import Ucos2Verify.VC.code.flag.spec.flag_del_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac_scope.
Local Open Scope sac.

(*----- Function OSFlagDel -----*)

Definition OSFlagDel_safety_wit_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (flag_del_source_cut sg caller before )) (PreH2 : (0 <= opt_pre)) (PreH3 : (opt_pre <= 255)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (pgrp_pre = pointer)) (PreH7 : (opt_pre = option)) (PreH8 : (perr_pre = error_address)) (PreH9 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH10 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH11 : (name = (LitMap (("?"%string))))) (PreH12 : (flag_del_build_context sg )) (PreH13 : (flag_del_stack_layout sg )) (PreH14 : (kernel_sched_ready_clients critical )) (PreH15 : (flag_del_argument sg pgrp_pre view before observed )) (PreH16 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (flag_del_closed environment local sg caller mask before )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_del_raw_type pgrp_pre view )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_2 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH11 : (view = (FlagQueryPool (id)))) (PreH12 : (flag_query_selected view acquired image )) (PreH13 : (flag_del_rechecked option image )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_3 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 0)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_query_selected view acquired image )) (PreH15 : (flag_del_rechecked option image )) (PreH16 : (tasks_waiting = (flag_del_waiting (image)))) (PreH17 : (flag_del_source_cut sg active acquired )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_4 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 0)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_query_selected view acquired image )) (PreH15 : (flag_del_rechecked option image )) (PreH16 : (tasks_waiting = (flag_del_waiting (image)))) (PreH17 : (flag_del_source_cut sg active acquired )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_5 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 false )
  **  ((error_address) # UChar  |-> 0)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_6 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (remaining_2: (@list Z)) (pnode_2: Z) (tasks_waiting_2: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (id_2: Z) (active_2: TaskSuspendCaller) (cpu_sr_2: Z) (visited_2: (@list Z)) (acquired_2: UCOS2_Verify_State) (protected_local_2: (Armv7aContinuation -> Assertion)) (current_2: UCOS2_Verify_State) (now_local_2: (Armv7aContinuation -> Assertion)) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr_2 acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting_2 = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 pnode_2 )) (PreH17 : (option = 1)) (PreH18 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH19 : (0 <= option)) (PreH20 : (option <= 255)) (PreH21 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH23 : (name = (LitMap (("?"%string))))) (PreH24 : (flag_del_build_context sg )) (PreH25 : (flag_del_stack_layout sg )) (PreH26 : (kernel_sched_ready_clients critical )) (PreH27 : (flag_del_argument sg pointer view before observed )) (PreH28 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH29 : (view = (FlagQueryPool (id)))) (PreH30 : (flag_del_acquired_group acquired id image order )) (PreH31 : (tasks_waiting = (flag_del_waiting (image)))) (PreH32 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_2)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting_2)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode_2)
  **  (flag_del_masked environment critical now_local_2 sg active_2 cpu_sr_2 acquired_2 current_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_7 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) (PreH17 : (flag_del_waiter_at current pnode waiter old )) (PreH18 : (flag_del_loan_origin current waiter original fragments )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode)
  **  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_8 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (drained: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (drained_image: FlagGroupImage) (order: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg order acquired protected_local drained now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active acquired id order order (@nil Z) drained 0 )) (PreH17 : (flag_query_selected view drained drained_image )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (drained_image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (drained)))
  **  (flag_del_group_frame environment critical now_local sg active cpu_sr acquired pointer id drained drained_image )
  **  ((error_address) # UChar  |->_)
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_9 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (drained: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (drained_image: FlagGroupImage) (order: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg order acquired protected_local drained now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active acquired id order order (@nil Z) drained 0 )) (PreH17 : (flag_query_selected view drained drained_image )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_del_free_head_state (sg) (drained)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (drained)))
  **  (flag_del_group_frame environment critical now_local sg active cpu_sr acquired pointer id drained drained_image )
  **  ((error_address) # UChar  |->_)
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_10 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (context: OsSchedCallContext) (current: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current )) (PreH13 : (flag_del_scheduler_safe environment critical sg context mask current 0 0 X )) (PreH14 : (flag_del_same_task_call context caller )) (PreH15 : (os_sched_active_local_stable (flag_del_source_active (sg)) )) ,
  (os_sched_active_history_return_post environment critical (flag_del_source_active (sg)) sg context mask current )
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((error_address) # UChar  |-> 0)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_safety_wit_11 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: bool) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 1)) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 scheduled )
  **  ((error_address) # UChar  |-> 0)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSFlagDel_entail_wit_1 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (source: FlagDelSourceABI) (PreH1 : (pgrp_pre = pointer)) (PreH2 : (opt_pre = option)) (PreH3 : (perr_pre = error_address)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pgrp_pre view before observed )) (PreH11 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (flag_del_source_public_entry source environment critical local sg caller mask before pgrp_pre view perr_pre F )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= opt_pre) ” 
  &&  “ (opt_pre <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pgrp_pre = pointer) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (perr_pre = error_address) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pgrp_pre view before observed ) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X ) ”
  &&  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (flag_del_source_public_entry source environment critical local sg caller mask before pgrp_pre view perr_pre F )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pgrp_pre = pointer)) (PreH4 : (opt_pre = option)) (PreH5 : (perr_pre = error_address)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pgrp_pre view before observed )) (PreH13 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  TT && emp 
|--
  “ (opt_pre <= 255) ” 
  &&  “ (0 <= opt_pre) ”
  &&  emp
).

Definition OSFlagDel_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pgrp_pre = pointer)) (PreH4 : (opt_pre = option)) (PreH5 : (perr_pre = error_address)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pgrp_pre view before observed )) (PreH13 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (opt_pre <= 255)
.

Definition OSFlagDel_entail_wit_1_split_goal_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (pgrp_pre = pointer)) (PreH4 : (opt_pre = option)) (PreH5 : (perr_pre = error_address)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pgrp_pre view before observed )) (PreH13 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (0 <= opt_pre)
.

Definition OSFlagDel_entail_wit_2 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pgrp_pre = 0)) (PreH2 : (flag_del_source_cut sg caller before )) (PreH3 : (0 <= opt_pre)) (PreH4 : (opt_pre <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pgrp_pre = pointer)) (PreH8 : (opt_pre = option)) (PreH9 : (perr_pre = error_address)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH12 : (name = (LitMap (("?"%string))))) (PreH13 : (flag_del_build_context sg )) (PreH14 : (flag_del_stack_layout sg )) (PreH15 : (kernel_sched_ready_clients critical )) (PreH16 : (flag_del_argument sg pgrp_pre view before observed )) (PreH17 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (flag_del_closed environment local sg caller mask before )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_del_raw_type pgrp_pre view )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 110)
  **  (F )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (110)) X )
  **  ((error_address) # UChar  |-> 110)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pgrp_pre = 0)) (PreH2 : (flag_del_source_cut sg caller before )) (PreH3 : (0 <= opt_pre)) (PreH4 : (opt_pre <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pgrp_pre = pointer)) (PreH8 : (opt_pre = option)) (PreH9 : (perr_pre = error_address)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH12 : (name = (LitMap (("?"%string))))) (PreH13 : (flag_del_build_context sg )) (PreH14 : (flag_del_stack_layout sg )) (PreH15 : (kernel_sched_ready_clients critical )) (PreH16 : (flag_del_argument sg pgrp_pre view before observed )) (PreH17 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (flag_del_closed environment local sg caller mask before )
  **  (flag_del_raw_type pgrp_pre view )
  **  (F )
  **  (GlobalStrings LitMap )
|--
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (110)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pgrp_pre = 0)) (PreH2 : (flag_del_source_cut sg caller before )) (PreH3 : (0 <= opt_pre)) (PreH4 : (opt_pre <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pgrp_pre = pointer)) (PreH8 : (opt_pre = option)) (PreH9 : (perr_pre = error_address)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH12 : (name = (LitMap (("?"%string))))) (PreH13 : (flag_del_build_context sg )) (PreH14 : (flag_del_stack_layout sg )) (PreH15 : (kernel_sched_ready_clients critical )) (PreH16 : (flag_del_argument sg pgrp_pre view before observed )) (PreH17 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (flag_del_closed environment local sg caller mask before )
  **  (flag_del_raw_type pgrp_pre view )
  **  (F )
  **  (GlobalStrings LitMap )
|--
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (110)) X )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_3 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (before))) (32)) > 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (flag_del_source_cut sg caller before )) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pgrp_pre = pointer)) (PreH9 : (opt_pre = option)) (PreH10 : (perr_pre = error_address)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH13 : (name = (LitMap (("?"%string))))) (PreH14 : (flag_del_build_context sg )) (PreH15 : (flag_del_stack_layout sg )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (flag_del_argument sg pgrp_pre view before observed )) (PreH18 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_del_raw_type pgrp_pre view )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 15)
  **  (F )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (15)) X )
  **  ((error_address) # UChar  |-> 15)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (before))) (32)) > 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (flag_del_source_cut sg caller before )) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pgrp_pre = pointer)) (PreH9 : (opt_pre = option)) (PreH10 : (perr_pre = error_address)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH13 : (name = (LitMap (("?"%string))))) (PreH14 : (flag_del_build_context sg )) (PreH15 : (flag_del_stack_layout sg )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (flag_del_argument sg pgrp_pre view before observed )) (PreH18 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
  **  (flag_del_raw_type pgrp_pre view )
  **  (F )
  **  (GlobalStrings LitMap )
|--
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (15)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (before))) (32)) > 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (flag_del_source_cut sg caller before )) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pgrp_pre = pointer)) (PreH9 : (opt_pre = option)) (PreH10 : (perr_pre = error_address)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH13 : (name = (LitMap (("?"%string))))) (PreH14 : (flag_del_build_context sg )) (PreH15 : (flag_del_stack_layout sg )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (flag_del_argument sg pgrp_pre view before observed )) (PreH18 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
  **  (flag_del_raw_type pgrp_pre view )
  **  (F )
  **  (GlobalStrings LitMap )
|--
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (15)) X )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_4 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (before))) (32)) <= 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (flag_del_source_cut sg caller before )) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pgrp_pre = pointer)) (PreH9 : (opt_pre = option)) (PreH10 : (perr_pre = error_address)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH13 : (name = (LitMap (("?"%string))))) (PreH14 : (flag_del_build_context sg )) (PreH15 : (flag_del_stack_layout sg )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (flag_del_argument sg pgrp_pre view before observed )) (PreH18 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_del_raw_type pgrp_pre view )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pointer option name before X ) ” 
  &&  “ (pointer <> 0) ” 
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  (flag_del_type_cut environment local sg caller mask pointer view before observed )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((os_sched_ints (before))) (32)) <= 0)) (PreH2 : (pgrp_pre <> 0)) (PreH3 : (flag_del_source_cut sg caller before )) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 255)) (PreH6 : (0 <= UINT_MAX)) (PreH7 : (0 >= 0)) (PreH8 : (pgrp_pre = pointer)) (PreH9 : (opt_pre = option)) (PreH10 : (perr_pre = error_address)) (PreH11 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH12 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH13 : (name = (LitMap (("?"%string))))) (PreH14 : (flag_del_build_context sg )) (PreH15 : (flag_del_stack_layout sg )) (PreH16 : (kernel_sched_ready_clients critical )) (PreH17 : (flag_del_argument sg pgrp_pre view before observed )) (PreH18 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
  **  (flag_del_raw_type pgrp_pre view )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
  **  (GlobalStrings LitMap )
|--
  EX (x: Z) ,
  “ (opt_pre = option) ” 
  &&  “ (perr_pre = error_address) ” 
  &&  “ (pgrp_pre = pointer) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pointer option name before X ) ” 
  &&  “ (pointer <> 0) ” 
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  ((error_address) # UChar  |-> x)
  **  (flag_del_type_cut environment local sg caller mask pointer view before observed )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_5 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH13 : (pointer <> 0)) (PreH14 : ((os_sched_ints (before)) = 0)) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pointer view before observed )
  **  ((error_address) # UChar  |-> 1)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (1)) X )
  **  ((error_address) # UChar  |-> 1)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH13 : (pointer <> 0)) (PreH14 : ((os_sched_ints (before)) = 0)) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pointer view before observed )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (1)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_5_split_goal_spatial := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) <> 5)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH13 : (pointer <> 0)) (PreH14 : ((os_sched_ints (before)) = 0)) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pointer view before observed )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (1)) X )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_6 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH13 : (pointer <> 0)) (PreH14 : ((os_sched_ints (before)) = 0)) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pointer view before observed )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (pointer <> 0) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pointer option name before X ) ”
  &&  (flag_del_closed environment local sg caller mask before )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH13 : (pointer <> 0)) (PreH14 : ((os_sched_ints (before)) = 0)) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pointer view before observed )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ ((flagImageType (observed)) = 5) ”
  &&  (flag_del_closed environment local sg caller mask before )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_6_split_goal_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH13 : (pointer <> 0)) (PreH14 : ((os_sched_ints (before)) = 0)) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pointer view before observed )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ ((flagImageType (observed)) = 5) ”
.

Definition OSFlagDel_entail_wit_6_split_goal_spatial := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : ((unsigned_last_nbits ((flagImageType (observed))) (32)) = 5)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH13 : (pointer <> 0)) (PreH14 : ((os_sched_ints (before)) = 0)) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pointer view before observed )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_closed environment local sg caller mask before )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_7 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (save_heap: model) (retval: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (pointer <> 0)) (PreH12 : ((os_sched_ints (before)) = 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) ,
  (flag_del_source_save_output environment critical local sg caller mask before save_heap retval )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active retval acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked_type_cut environment critical protected_local sg active retval acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (save_heap: model) (retval: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (pointer <> 0)) (PreH12 : ((os_sched_ints (before)) = 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) ,
  (flag_del_source_save_output environment critical local sg caller mask before save_heap retval )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active retval acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked_type_cut environment critical protected_local sg active retval acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_8 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  (flag_del_masked_type_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_del_masked_type_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  (flag_del_masked_type_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_del_masked_type_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_9_1 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (option = 1)) (PreH3 : (option <> 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH14 : (view = (FlagQueryPool (id)))) (PreH15 : (flag_query_selected view acquired_2 image )) (PreH16 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (option = 1)) (PreH3 : (option <> 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH14 : (view = (FlagQueryPool (id)))) (PreH15 : (flag_query_selected view acquired_2 image )) (PreH16 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_9_2 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_query_selected view acquired_2 image )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image))) (32)) <> 5)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_query_selected view acquired_2 image )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_10 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH11 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH12 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ”
  &&  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 1 false )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH11 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH12 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 1 false )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_10_split_goal_spatial := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH11 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH12 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 1 false )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_11 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 1 false )
  **  ((error_address) # UChar  |-> 1)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical protected_local sg caller returned mask pointer view option name before current (pair (pointer) (1)) X )
  **  ((error_address) # UChar  |-> 1)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 1 false )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical protected_local sg caller returned mask pointer view option name before current (pair (pointer) (1)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_12_1 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : (option <> 1)) (PreH2 : (option <> 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_query_selected view acquired_2 image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : (option <> 1)) (PreH2 : (option <> 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_query_selected view acquired_2 image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_12_2 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image_2))) (32)) = 5)) (PreH2 : (option = 1)) (PreH3 : (option <> 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH14 : (view = (FlagQueryPool (id_2)))) (PreH15 : (flag_query_selected view acquired_2 image_2 )) (PreH16 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image_2))) (32)) = 5)) (PreH2 : (option = 1)) (PreH3 : (option <> 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH14 : (view = (FlagQueryPool (id_2)))) (PreH15 : (flag_query_selected view acquired_2 image_2 )) (PreH16 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_12_3 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image_2))) (32)) = 5)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_query_selected view acquired_2 image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((unsigned_last_nbits ((flagImageType (image_2))) (32)) = 5)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_query_selected view acquired_2 image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  (flag_del_masked_type_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_13 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_rechecked option image_2 )) (PreH14 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_rechecked option image_2 )) (PreH14 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_14_1 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((flagImageHead (image_2)) <> 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH12 : (view = (FlagQueryPool (id_2)))) (PreH13 : (flag_query_selected view acquired_2 image_2 )) (PreH14 : (flag_del_rechecked option image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image_2)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (1 = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((flagImageHead (image_2)) <> 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH12 : (view = (FlagQueryPool (id_2)))) (PreH13 : (flag_query_selected view acquired_2 image_2 )) (PreH14 : (flag_del_rechecked option image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image_2)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (1 = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_14_2 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((flagImageHead (image_2)) = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH12 : (view = (FlagQueryPool (id_2)))) (PreH13 : (flag_query_selected view acquired_2 image_2 )) (PreH14 : (flag_del_rechecked option image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image_2)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (0 = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (PreH1 : ((flagImageHead (image_2)) = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH12 : (view = (FlagQueryPool (id_2)))) (PreH13 : (flag_query_selected view acquired_2 image_2 )) (PreH14 : (flag_del_rechecked option image_2 )) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image_2)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (0 = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_group_cut environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_15 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_rechecked option image_2 )) (PreH14 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) (PreH16 : (0 = option)) ,
  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_rechecked option image_2 )) (PreH14 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) (PreH16 : (0 = option)) ,
  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_16 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 0)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_query_selected view acquired_2 image_2 )) (PreH15 : (flag_del_rechecked option image_2 )) (PreH16 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH17 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pointer)
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ” 
  &&  “ (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 0)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_query_selected view acquired_2 image_2 )) (PreH15 : (flag_del_rechecked option image_2 )) (PreH16 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH17 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  (GlobalStrings LitMap )
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pointer)
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ” 
  &&  “ (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_17 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (view = (FlagQueryPool (id)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH14 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) ((LitMap (("?"%string))))) false restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ”
  &&  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 false )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (view = (FlagQueryPool (id)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH14 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) ((LitMap (("?"%string))))) false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 false )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_17_split_goal_spatial := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (view = (FlagQueryPool (id)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH14 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) ((LitMap (("?"%string))))) false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 false )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_18 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 0)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_query_selected view acquired_2 image )) (PreH15 : (flag_del_rechecked option image )) (PreH16 : (tasks_waiting = (flag_del_waiting (image)))) (PreH17 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 0)) (PreH2 : (option = 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_query_selected view acquired_2 image )) (PreH15 : (flag_del_rechecked option image )) (PreH16 : (tasks_waiting = (flag_del_waiting (image)))) (PreH17 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_19 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH13 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ”
  &&  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 73 false )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH13 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 73 false )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_19_split_goal_spatial := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH13 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 73 false )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_20 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_rechecked option image_2 )) (PreH14 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) (PreH16 : (0 <> option)) (PreH17 : (1 = option)) ,
  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id_2)))) (PreH12 : (flag_query_selected view acquired_2 image_2 )) (PreH13 : (flag_del_rechecked option image_2 )) (PreH14 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) (PreH16 : (0 <> option)) (PreH17 : (1 = option)) ,
  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_query_selected view acquired image ) ” 
  &&  “ (flag_del_rechecked option image ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired)))
  **  (flag_del_group_frame environment critical protected_local sg active cpu_sr acquired pointer id acquired image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_21 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH12 : (view = (FlagQueryPool (id_2)))) (PreH13 : (flag_query_selected view acquired_2 image )) (PreH14 : (flag_del_rechecked option image )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (remaining: (@list Z))  (image_2: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image_2 order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image_2))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current (flagImageHead (image)) ) ”
  &&  (flag_del_masked environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id_2: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH12 : (view = (FlagQueryPool (id_2)))) (PreH13 : (flag_query_selected view acquired_2 image )) (PreH14 : (flag_del_rechecked option image )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_cut sg active_2 acquired_2 )) ,
  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (acquired_2)))
  **  (flag_del_group_frame environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 acquired_2 image )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (remaining: (@list Z))  (image_2: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image_2 order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image_2))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current (flagImageHead (image)) ) ”
  &&  (flag_del_masked environment critical now_local sg active cpu_sr acquired current )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_22 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) ,
  (flag_del_masked environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (remaining_2: (@list Z))  (image_2: FlagGroupImage)  (order_2: (@list Z))  (id_2: Z)  (active_2: TaskSuspendCaller)  (visited_2: (@list Z))  (acquired_2: UCOS2_Verify_State)  (protected_local_2: (Armv7aContinuation -> Assertion))  (current_2: UCOS2_Verify_State)  (now_local_2: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X ) ” 
  &&  “ (view = (FlagQueryPool (id_2))) ” 
  &&  “ (flag_del_acquired_group acquired_2 id_2 image_2 order_2 ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image_2))) ” 
  &&  “ (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 pnode ) ” 
  &&  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ”
  &&  (flag_del_masked environment critical now_local_2 sg active_2 cpu_sr acquired_2 current_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) ,
  TT && emp 
|--
  EX (remaining_2: (@list Z))  (image_2: FlagGroupImage)  (order_2: (@list Z))  (id_2: Z)  (visited_2: (@list Z))  (protected_local_2: (Armv7aContinuation -> Assertion)) ,
  “ (flag_del_local_prefix sg visited_2 acquired protected_local_2 current now_local ) ” 
  &&  “ ((FlagQueryPool (id)) = (FlagQueryPool (id_2))) ” 
  &&  “ (flag_del_acquired_group acquired id_2 image_2 order_2 ) ” 
  &&  “ ((flag_del_waiting (image)) = (flag_del_waiting (image_2))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id_2 order_2 visited_2 remaining_2 current pnode ) ”
  &&  emp
).

Definition OSFlagDel_entail_wit_23 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr_2: Z) (tasks_waiting_2: Z) (pnode_2: Z) (remaining_3: (@list Z)) (pnode: Z) (tasks_waiting: Z) (image_3: FlagGroupImage) (order_3: (@list Z)) (id_3: Z) (active_3: TaskSuspendCaller) (cpu_sr: Z) (visited_3: (@list Z)) (acquired_3: UCOS2_Verify_State) (protected_local_3: (Armv7aContinuation -> Assertion)) (current_3: UCOS2_Verify_State) (now_local_3: (Armv7aContinuation -> Assertion)) (PreH1 : (pnode <> 0)) (PreH2 : (option = 1)) (PreH3 : (flag_del_local_prefix sg visited_3 acquired_3 protected_local_3 current_3 now_local_3 )) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_3 cpu_sr acquired_3 X )) (PreH14 : (view = (FlagQueryPool (id_3)))) (PreH15 : (flag_del_acquired_group acquired_3 id_3 image_3 order_3 )) (PreH16 : (tasks_waiting = (flag_del_waiting (image_3)))) (PreH17 : (flag_del_source_loop_facts sg active_3 acquired_3 id_3 order_3 visited_3 remaining_3 current_3 pnode )) (PreH18 : (option = 1)) (PreH19 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 )) (PreH20 : (0 <= option)) (PreH21 : (option <= 255)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH24 : (name = (LitMap (("?"%string))))) (PreH25 : (flag_del_build_context sg )) (PreH26 : (flag_del_stack_layout sg )) (PreH27 : (kernel_sched_ready_clients critical )) (PreH28 : (flag_del_argument sg pointer view before observed )) (PreH29 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr_2 acquired_2 X )) (PreH30 : (view = (FlagQueryPool (id_2)))) (PreH31 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH32 : (tasks_waiting_2 = (flag_del_waiting (image_2)))) (PreH33 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 pnode_2 )) ,
  (flag_del_masked environment critical now_local_3 sg active_3 cpu_sr acquired_3 current_3 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (original: TaskStackLease)  (fragments: TaskStackFragments)  (waiter: FlagWaiterState)  (old: TaskAbstractState)  (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ” 
  &&  “ (flag_del_waiter_at current pnode waiter old ) ” 
  &&  “ (flag_del_loan_origin current waiter original fragments ) ”
  &&  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr_2: Z) (tasks_waiting_2: Z) (pnode_2: Z) (remaining_3: (@list Z)) (pnode: Z) (tasks_waiting: Z) (image_3: FlagGroupImage) (order_3: (@list Z)) (id_3: Z) (active_3: TaskSuspendCaller) (cpu_sr: Z) (visited_3: (@list Z)) (acquired_3: UCOS2_Verify_State) (protected_local_3: (Armv7aContinuation -> Assertion)) (current_3: UCOS2_Verify_State) (now_local_3: (Armv7aContinuation -> Assertion)) (PreH1 : (pnode <> 0)) (PreH2 : (option = 1)) (PreH3 : (flag_del_local_prefix sg visited_3 acquired_3 protected_local_3 current_3 now_local_3 )) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_3 cpu_sr acquired_3 X )) (PreH14 : (view = (FlagQueryPool (id_3)))) (PreH15 : (flag_del_acquired_group acquired_3 id_3 image_3 order_3 )) (PreH16 : (tasks_waiting = (flag_del_waiting (image_3)))) (PreH17 : (flag_del_source_loop_facts sg active_3 acquired_3 id_3 order_3 visited_3 remaining_3 current_3 pnode )) (PreH18 : (option = 1)) (PreH19 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 )) (PreH20 : (0 <= option)) (PreH21 : (option <= 255)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH24 : (name = (LitMap (("?"%string))))) (PreH25 : (flag_del_build_context sg )) (PreH26 : (flag_del_stack_layout sg )) (PreH27 : (kernel_sched_ready_clients critical )) (PreH28 : (flag_del_argument sg pointer view before observed )) (PreH29 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr_2 acquired_2 X )) (PreH30 : (view = (FlagQueryPool (id_2)))) (PreH31 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH32 : (tasks_waiting_2 = (flag_del_waiting (image_2)))) (PreH33 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 pnode_2 )) ,
  (flag_del_masked environment critical now_local_3 sg active_3 cpu_sr acquired_3 current_3 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (original: TaskStackLease)  (fragments: TaskStackFragments)  (waiter: FlagWaiterState)  (old: TaskAbstractState)  (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ” 
  &&  “ (flag_del_waiter_at current pnode waiter old ) ” 
  &&  “ (flag_del_loan_origin current waiter original fragments ) ”
  &&  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_24 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (waiter_2: FlagWaiterState) (old_2: TaskAbstractState) (original_2: TaskStackLease) (fragments_2: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (retval: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 pnode )) (PreH17 : (flag_del_waiter_at current_2 pnode waiter_2 old_2 )) (PreH18 : (flag_del_loan_origin current_2 waiter_2 original_2 fragments_2 )) ,
  (flag_task_rdy_fields_post sg current_2 pnode waiter_2 0 PendAbort retval )
  **  (F )
  **  (flag_del_iteration_frame environment critical now_local_2 sg active_2 cpu_sr acquired_2 current_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  EX (post: UCOS2_Verify_State)  (original: TaskStackLease)  (fragments: TaskStackFragments)  (waiter: FlagWaiterState)  (old: TaskAbstractState)  (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ” 
  &&  “ (flag_del_waiter_at current pnode waiter old ) ” 
  &&  “ (flag_del_loan_origin post waiter original fragments ) ” 
  &&  “ (flag_del_step sg current pnode post ) ”
  &&  (flag_del_iteration_next environment critical now_local sg active cpu_sr acquired post pnode waiter )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (waiter_2: FlagWaiterState) (old_2: TaskAbstractState) (original_2: TaskStackLease) (fragments_2: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (retval: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 pnode )) (PreH17 : (flag_del_waiter_at current_2 pnode waiter_2 old_2 )) (PreH18 : (flag_del_loan_origin current_2 waiter_2 original_2 fragments_2 )) ,
  (flag_task_rdy_fields_post sg current_2 pnode waiter_2 0 PendAbort retval )
  **  (F )
  **  (flag_del_iteration_frame environment critical now_local_2 sg active_2 cpu_sr acquired_2 current_2 )
  **  (GlobalStrings LitMap )
|--
  EX (post: UCOS2_Verify_State)  (original: TaskStackLease)  (fragments: TaskStackFragments)  (waiter: FlagWaiterState)  (old: TaskAbstractState)  (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ” 
  &&  “ (flag_del_waiter_at current pnode waiter old ) ” 
  &&  “ (flag_del_loan_origin post waiter original fragments ) ” 
  &&  “ (flag_del_step sg current pnode post ) ”
  &&  (flag_del_iteration_next environment critical now_local sg active cpu_sr acquired post pnode waiter )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_25 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current_2: UCOS2_Verify_State) (post_2: UCOS2_Verify_State) (id_2: Z) (node: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (waiter_2: FlagWaiterState) (old_2: TaskAbstractState) (original_2: TaskStackLease) (fragments_2: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 node )) (PreH17 : (flag_del_waiter_at current_2 node waiter_2 old_2 )) (PreH18 : (flag_del_loan_origin post_2 waiter_2 original_2 fragments_2 )) (PreH19 : (flag_del_step sg current_2 node post_2 )) ,
  (flag_del_iteration_next environment critical now_local_2 sg active_2 cpu_sr acquired_2 post_2 node waiter_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (post: UCOS2_Verify_State)  (original: TaskStackLease)  (fragments: TaskStackFragments)  (waiter: FlagWaiterState)  (old: TaskAbstractState)  (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current node ) ” 
  &&  “ (flag_del_waiter_at current node waiter old ) ” 
  &&  “ (flag_del_loan_origin post waiter original fragments ) ” 
  &&  “ (flag_del_step sg current node post ) ”
  &&  ((&((node)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_del_node_next (waiter)))
  **  (flag_del_iteration_next_frame environment critical now_local sg active cpu_sr acquired post node waiter )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current_2: UCOS2_Verify_State) (post_2: UCOS2_Verify_State) (id_2: Z) (node: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (waiter_2: FlagWaiterState) (old_2: TaskAbstractState) (original_2: TaskStackLease) (fragments_2: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 node )) (PreH17 : (flag_del_waiter_at current_2 node waiter_2 old_2 )) (PreH18 : (flag_del_loan_origin post_2 waiter_2 original_2 fragments_2 )) (PreH19 : (flag_del_step sg current_2 node post_2 )) ,
  (flag_del_iteration_next environment critical now_local_2 sg active_2 cpu_sr acquired_2 post_2 node waiter_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (post: UCOS2_Verify_State)  (original: TaskStackLease)  (fragments: TaskStackFragments)  (waiter: FlagWaiterState)  (old: TaskAbstractState)  (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current node ) ” 
  &&  “ (flag_del_waiter_at current node waiter old ) ” 
  &&  “ (flag_del_loan_origin post waiter original fragments ) ” 
  &&  “ (flag_del_step sg current node post ) ”
  &&  ((&((node)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_del_node_next (waiter)))
  **  (flag_del_iteration_next_frame environment critical now_local sg active cpu_sr acquired post node waiter )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_26 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (post_2: UCOS2_Verify_State) (id_2: Z) (node: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current node )) (PreH17 : (flag_del_waiter_at current node waiter old )) (PreH18 : (flag_del_loan_origin post_2 waiter original fragments )) (PreH19 : (flag_del_step sg current node post_2 )) ,
  ((&((node)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_del_node_next (waiter)))
  **  (flag_del_iteration_next_frame environment critical now_local sg active_2 cpu_sr acquired_2 post_2 node waiter )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (post: UCOS2_Verify_State)  (next_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local post next_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining post (flag_del_node_next (waiter)) ) ”
  &&  (flag_del_masked environment critical next_local sg active cpu_sr acquired post )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (post_2: UCOS2_Verify_State) (id_2: Z) (node: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited_2: (@list Z)) (remaining_2: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current node )) (PreH17 : (flag_del_waiter_at current node waiter old )) (PreH18 : (flag_del_loan_origin post_2 waiter original fragments )) (PreH19 : (flag_del_step sg current node post_2 )) ,
  ((&((node)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_del_node_next (waiter)))
  **  (flag_del_iteration_next_frame environment critical now_local sg active_2 cpu_sr acquired_2 post_2 node waiter )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (remaining: (@list Z))  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (post: UCOS2_Verify_State)  (next_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local post next_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining post (flag_del_node_next (waiter)) ) ”
  &&  (flag_del_masked environment critical next_local sg active cpu_sr acquired post )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_27 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_3: (Armv7aContinuation -> Assertion)) (active_3: TaskSuspendCaller) (acquired_3: UCOS2_Verify_State) (post: UCOS2_Verify_State) (id_3: Z) (image_3: FlagGroupImage) (order_3: (@list Z)) (visited_3: (@list Z)) (remaining_3: (@list Z)) (next_local: (Armv7aContinuation -> Assertion)) (cpu_sr_2: Z) (tasks_waiting_2: Z) (pnode_2: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_3 acquired_3 protected_local_3 post next_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_3 cpu_sr_2 acquired_3 X )) (PreH13 : (view = (FlagQueryPool (id_3)))) (PreH14 : (flag_del_acquired_group acquired_3 id_3 image_3 order_3 )) (PreH15 : (tasks_waiting_2 = (flag_del_waiting (image_3)))) (PreH16 : (flag_del_source_loop_facts sg active_3 acquired_3 id_3 order_3 visited_3 remaining_3 post pnode_2 )) ,
  (flag_del_masked environment critical next_local sg active_3 cpu_sr_2 acquired_3 post )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (remaining_2: (@list Z))  (image_2: FlagGroupImage)  (order_2: (@list Z))  (id_2: Z)  (active_2: TaskSuspendCaller)  (visited_2: (@list Z))  (acquired_2: UCOS2_Verify_State)  (protected_local_2: (Armv7aContinuation -> Assertion))  (current_2: UCOS2_Verify_State)  (now_local_2: (Armv7aContinuation -> Assertion))  (remaining: (@list Z))  (pnode: Z)  (tasks_waiting: Z)  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (cpu_sr: Z)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited_2 acquired_2 protected_local_2 current_2 now_local_2 ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr_2 acquired_2 X ) ” 
  &&  “ (view = (FlagQueryPool (id_2))) ” 
  &&  “ (flag_del_acquired_group acquired_2 id_2 image_2 order_2 ) ” 
  &&  “ (tasks_waiting_2 = (flag_del_waiting (image_2))) ” 
  &&  “ (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited_2 remaining_2 current_2 pnode_2 ) ” 
  &&  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ”
  &&  (flag_del_masked environment critical now_local_2 sg active_2 cpu_sr_2 acquired_2 current_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_3: (Armv7aContinuation -> Assertion)) (active_3: TaskSuspendCaller) (acquired_3: UCOS2_Verify_State) (post: UCOS2_Verify_State) (id_3: Z) (image_3: FlagGroupImage) (order_3: (@list Z)) (visited_3: (@list Z)) (remaining_3: (@list Z)) (next_local: (Armv7aContinuation -> Assertion)) (cpu_sr_2: Z) (tasks_waiting_2: Z) (pnode_2: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited_3 acquired_3 protected_local_3 post next_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_3 cpu_sr_2 acquired_3 X )) (PreH13 : (view = (FlagQueryPool (id_3)))) (PreH14 : (flag_del_acquired_group acquired_3 id_3 image_3 order_3 )) (PreH15 : (tasks_waiting_2 = (flag_del_waiting (image_3)))) (PreH16 : (flag_del_source_loop_facts sg active_3 acquired_3 id_3 order_3 visited_3 remaining_3 post pnode_2 )) ,
  TT && emp 
|--
  EX (remaining_2: (@list Z))  (image_2: FlagGroupImage)  (order_2: (@list Z))  (id_2: Z)  (visited_2: (@list Z))  (protected_local_2: (Armv7aContinuation -> Assertion))  (remaining: (@list Z))  (pnode: Z)  (image: FlagGroupImage)  (order: (@list Z))  (id: Z)  (active: TaskSuspendCaller)  (cpu_sr: Z)  (visited: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (current: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (flag_del_local_prefix sg visited_2 acquired_3 protected_local_2 post next_local ) ” 
  &&  “ ((FlagQueryPool (id_3)) = (FlagQueryPool (id_2))) ” 
  &&  “ (flag_del_acquired_group acquired_3 id_2 image_2 order_2 ) ” 
  &&  “ ((flag_del_waiting (image_3)) = (flag_del_waiting (image_2))) ” 
  &&  “ (flag_del_source_loop_facts sg active_3 acquired_3 id_2 order_2 visited_2 remaining_2 post pnode_2 ) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask (FlagQueryPool (id_3)) pointer 1 (LitMap (("?"%string))) before observed active cpu_sr acquired X ) ” 
  &&  “ ((FlagQueryPool (id_3)) = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ”
  &&  emp
).

Definition OSFlagDel_entail_wit_28 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr_2: Z) (tasks_waiting_2: Z) (pnode: Z) (remaining_2: (@list Z)) (pnode_2: Z) (tasks_waiting: Z) (image_3: FlagGroupImage) (order_3: (@list Z)) (id_3: Z) (active_3: TaskSuspendCaller) (cpu_sr: Z) (visited_2: (@list Z)) (acquired_3: UCOS2_Verify_State) (protected_local_3: (Armv7aContinuation -> Assertion)) (current_2: UCOS2_Verify_State) (now_local_3: (Armv7aContinuation -> Assertion)) (PreH1 : (pnode_2 = 0)) (PreH2 : (option = 1)) (PreH3 : (flag_del_local_prefix sg visited_2 acquired_3 protected_local_3 current_2 now_local_3 )) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_3 cpu_sr acquired_3 X )) (PreH14 : (view = (FlagQueryPool (id_3)))) (PreH15 : (flag_del_acquired_group acquired_3 id_3 image_3 order_3 )) (PreH16 : (tasks_waiting = (flag_del_waiting (image_3)))) (PreH17 : (flag_del_source_loop_facts sg active_3 acquired_3 id_3 order_3 visited_2 remaining_2 current_2 pnode_2 )) (PreH18 : (option = 1)) (PreH19 : (flag_del_local_prefix sg visited acquired_2 protected_local_2 current now_local_2 )) (PreH20 : (0 <= option)) (PreH21 : (option <= 255)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH24 : (name = (LitMap (("?"%string))))) (PreH25 : (flag_del_build_context sg )) (PreH26 : (flag_del_stack_layout sg )) (PreH27 : (kernel_sched_ready_clients critical )) (PreH28 : (flag_del_argument sg pointer view before observed )) (PreH29 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr_2 acquired_2 X )) (PreH30 : (view = (FlagQueryPool (id_2)))) (PreH31 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH32 : (tasks_waiting_2 = (flag_del_waiting (image_2)))) (PreH33 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited remaining current pnode )) ,
  ((( &( "pnode" ) )) # Ptr  |-> pnode_2)
  **  (flag_del_masked environment critical now_local_3 sg active_3 cpu_sr acquired_3 current_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (drained_image: FlagGroupImage)  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (order: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (drained: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg order acquired protected_local drained now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order order (@nil Z) drained 0 ) ” 
  &&  “ (flag_query_selected view drained drained_image ) ”
  &&  (flag_del_group_cut environment critical now_local sg active cpu_sr acquired pointer id drained drained_image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (order_2: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr_2: Z) (tasks_waiting_2: Z) (pnode: Z) (remaining_2: (@list Z)) (pnode_2: Z) (tasks_waiting: Z) (image_3: FlagGroupImage) (order_3: (@list Z)) (id_3: Z) (active_3: TaskSuspendCaller) (cpu_sr: Z) (visited_2: (@list Z)) (acquired_3: UCOS2_Verify_State) (protected_local_3: (Armv7aContinuation -> Assertion)) (current_2: UCOS2_Verify_State) (now_local_3: (Armv7aContinuation -> Assertion)) (PreH1 : (pnode_2 = 0)) (PreH2 : (option = 1)) (PreH3 : (flag_del_local_prefix sg visited_2 acquired_3 protected_local_3 current_2 now_local_3 )) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_3 cpu_sr acquired_3 X )) (PreH14 : (view = (FlagQueryPool (id_3)))) (PreH15 : (flag_del_acquired_group acquired_3 id_3 image_3 order_3 )) (PreH16 : (tasks_waiting = (flag_del_waiting (image_3)))) (PreH17 : (flag_del_source_loop_facts sg active_3 acquired_3 id_3 order_3 visited_2 remaining_2 current_2 pnode_2 )) (PreH18 : (option = 1)) (PreH19 : (flag_del_local_prefix sg visited acquired_2 protected_local_2 current now_local_2 )) (PreH20 : (0 <= option)) (PreH21 : (option <= 255)) (PreH22 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH23 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH24 : (name = (LitMap (("?"%string))))) (PreH25 : (flag_del_build_context sg )) (PreH26 : (flag_del_stack_layout sg )) (PreH27 : (kernel_sched_ready_clients critical )) (PreH28 : (flag_del_argument sg pointer view before observed )) (PreH29 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr_2 acquired_2 X )) (PreH30 : (view = (FlagQueryPool (id_2)))) (PreH31 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH32 : (tasks_waiting_2 = (flag_del_waiting (image_2)))) (PreH33 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 visited remaining current pnode )) ,
  (flag_del_masked environment critical now_local_3 sg active_3 cpu_sr acquired_3 current_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (drained_image: FlagGroupImage)  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (order: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (drained: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg order acquired protected_local drained now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order order (@nil Z) drained 0 ) ” 
  &&  “ (flag_query_selected view drained drained_image ) ”
  &&  (flag_del_group_cut environment critical now_local sg active cpu_sr acquired pointer id drained drained_image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_29 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (drained_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (drained_image_2: FlagGroupImage) (order_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg order_2 acquired_2 protected_local_2 drained_2 now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 order_2 (@nil Z) drained_2 0 )) (PreH17 : (flag_query_selected view drained_2 drained_image_2 )) ,
  (flag_del_group_cut environment critical now_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 drained_2 drained_image_2 )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (drained_image: FlagGroupImage)  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (order: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (drained: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg order acquired protected_local drained now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order order (@nil Z) drained 0 ) ” 
  &&  “ (flag_query_selected view drained drained_image ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (drained_image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (drained)))
  **  (flag_del_group_frame environment critical now_local sg active cpu_sr acquired pointer id drained drained_image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (drained_2: UCOS2_Verify_State) (id_2: Z) (image_2: FlagGroupImage) (drained_image_2: FlagGroupImage) (order_2: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg order_2 acquired_2 protected_local_2 drained_2 now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id_2)))) (PreH14 : (flag_del_acquired_group acquired_2 id_2 image_2 order_2 )) (PreH15 : (tasks_waiting = (flag_del_waiting (image_2)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id_2 order_2 order_2 (@nil Z) drained_2 0 )) (PreH17 : (flag_query_selected view drained_2 drained_image_2 )) ,
  (flag_del_group_cut environment critical now_local_2 sg active_2 cpu_sr acquired_2 pointer id_2 drained_2 drained_image_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (drained_image: FlagGroupImage)  (image: FlagGroupImage)  (id: Z)  (active: TaskSuspendCaller)  (order: (@list Z))  (acquired: UCOS2_Verify_State)  (protected_local: (Armv7aContinuation -> Assertion))  (drained: UCOS2_Verify_State)  (now_local: (Armv7aContinuation -> Assertion)) ,
  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg order acquired protected_local drained now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order order (@nil Z) drained 0 ) ” 
  &&  “ (flag_query_selected view drained drained_image ) ”
  &&  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flagImageHead (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> (flagImageBits (drained_image)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> (flagImageName (drained_image)))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (flag_del_free_head_state (sg) (drained)))
  **  (flag_del_group_frame environment critical now_local sg active cpu_sr acquired pointer id drained drained_image )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_30 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (drained: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (drained_image: FlagGroupImage) (order: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg order acquired_2 protected_local drained now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired_2 id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id order order (@nil Z) drained 0 )) (PreH17 : (flag_query_selected view drained drained_image )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_del_free_head_state (sg) (drained)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pointer)
  **  (flag_del_group_frame environment critical now_local_2 sg active_2 cpu_sr acquired_2 pointer id drained drained_image )
  **  ((error_address) # UChar  |->_)
  **  (F )
|--
  EX (now_local: (Armv7aContinuation -> Assertion))  (released: UCOS2_Verify_State)  (scheduled: bool)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (scheduled = (flag_del_schedule_bit (tasks_waiting))) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released ) ” 
  &&  “ (flag_del_source_cut sg active released ) ”
  &&  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (drained: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (drained_image: FlagGroupImage) (order: (@list Z)) (now_local_2: (Armv7aContinuation -> Assertion)) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg order acquired_2 protected_local drained now_local_2 )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired_2 id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active_2 acquired_2 id order order (@nil Z) drained 0 )) (PreH17 : (flag_query_selected view drained drained_image )) ,
  (GlobalStrings LitMap )
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_del_free_head_state (sg) (drained)))
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagFlags")) # UShort  |-> 0)
  **  ((&((pointer)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> pointer)
  **  (flag_del_group_frame environment critical now_local_2 sg active_2 cpu_sr acquired_2 pointer id drained drained_image )
  **  (F )
|--
  EX (now_local: (Armv7aContinuation -> Assertion))  (released: UCOS2_Verify_State)  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 (flag_del_schedule_bit (tasks_waiting)) released ) ” 
  &&  “ (flag_del_source_cut sg active released ) ”
  &&  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_31 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled_2: bool) (restore_heap: model) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (scheduled_2 = (flag_del_schedule_bit (tasks_waiting)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled_2 released )) (PreH14 : (flag_del_source_cut sg active released )) ,
  (flag_del_source_restore_output environment critical now_local sg active cpu_sr acquired released (flag_del_schedule_bit (tasks_waiting)) restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (scheduled: bool) ,
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (scheduled = (flag_del_schedule_bit (tasks_waiting))) ”
  &&  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 scheduled )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled_2: bool) (restore_heap: model) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (scheduled_2 = (flag_del_schedule_bit (tasks_waiting)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled_2 released )) (PreH14 : (flag_del_source_cut sg active released )) ,
  (flag_del_source_restore_output environment critical now_local sg active cpu_sr acquired released (flag_del_schedule_bit (tasks_waiting)) restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 (flag_del_schedule_bit (tasks_waiting)) )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_31_split_goal_spatial := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled_2: bool) (restore_heap: model) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (scheduled_2 = (flag_del_schedule_bit (tasks_waiting)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled_2 released )) (PreH14 : (flag_del_source_cut sg active released )) ,
  (flag_del_source_restore_output environment critical now_local sg active cpu_sr acquired released (flag_del_schedule_bit (tasks_waiting)) restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 (flag_del_schedule_bit (tasks_waiting)) )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_32 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: bool) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) ,
  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 scheduled )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (now_local: (Armv7aContinuation -> Assertion))  (context: OsSchedCallContext)  (current: UCOS2_Verify_State) ,
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current ) ” 
  &&  “ (flag_del_scheduler_safe environment critical sg context mask current 0 0 X ) ” 
  &&  “ (flag_del_same_task_call context caller ) ” 
  &&  “ (os_sched_active_local_stable (flag_del_source_active (sg)) ) ”
  &&  (os_sched_active_call_pre environment now_local (flag_del_source_active (sg)) sg context mask current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: bool) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) = 1)) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 scheduled )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (now_local: (Armv7aContinuation -> Assertion))  (context: OsSchedCallContext)  (current: UCOS2_Verify_State) ,
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current ) ” 
  &&  “ (flag_del_scheduler_safe environment critical sg context mask current 0 0 X ) ” 
  &&  “ (flag_del_same_task_call context caller ) ” 
  &&  “ (os_sched_active_local_stable (flag_del_source_active (sg)) ) ”
  &&  (os_sched_active_call_pre environment now_local (flag_del_source_active (sg)) sg context mask current )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_33 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (option <> 0) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ”
  &&  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 7 false )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 7 false )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_33_split_goal_spatial := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_source_restore_output environment critical protected_local sg active cpu_sr acquired acquired false restore_heap )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 7 false )
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_entail_wit_34 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id)))) (PreH12 : (flag_query_selected view acquired_2 image )) (PreH13 : (flag_del_rechecked option image )) (PreH14 : (tasks_waiting = (flag_del_waiting (image)))) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) (PreH16 : (0 <> option)) (PreH17 : (1 <> option)) ,
  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option <> 0) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local_2: (Armv7aContinuation -> Assertion)) (active_2: TaskSuspendCaller) (acquired_2: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (tasks_waiting: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active_2 cpu_sr acquired_2 X )) (PreH11 : (view = (FlagQueryPool (id)))) (PreH12 : (flag_query_selected view acquired_2 image )) (PreH13 : (flag_del_rechecked option image )) (PreH14 : (tasks_waiting = (flag_del_waiting (image)))) (PreH15 : (flag_del_source_cut sg active_2 acquired_2 )) (PreH16 : (0 <> option)) (PreH17 : (1 <> option)) ,
  (flag_del_group_cut environment critical protected_local_2 sg active_2 cpu_sr acquired_2 pointer id acquired_2 image )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (protected_local: (Armv7aContinuation -> Assertion))  (active: TaskSuspendCaller)  (acquired: UCOS2_Verify_State) ,
  “ (option <> 0) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_35_1 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 false )
  **  ((error_address) # UChar  |-> 0)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (0) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 false )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (0) (0)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_35_2 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 73 false )
  **  ((error_address) # UChar  |-> 73)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 73 false )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (73)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_35_3 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (context: OsSchedCallContext) (current_2: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current_2 )) (PreH13 : (flag_del_scheduler_safe environment critical sg context mask current_2 0 0 X )) (PreH14 : (flag_del_same_task_call context caller )) (PreH15 : (os_sched_active_local_stable (flag_del_source_active (sg)) )) ,
  (os_sched_active_history_return_post environment critical (flag_del_source_active (sg)) sg context mask current_2 )
  **  ((error_address) # UChar  |-> 0)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (0) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (context: OsSchedCallContext) (current_2: UCOS2_Verify_State) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current_2 )) (PreH13 : (flag_del_scheduler_safe environment critical sg context mask current_2 0 0 X )) (PreH14 : (flag_del_same_task_call context caller )) (PreH15 : (os_sched_active_local_stable (flag_del_source_active (sg)) )) ,
  (os_sched_active_history_return_post environment critical (flag_del_source_active (sg)) sg context mask current_2 )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (0) (0)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_35_4 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: bool) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 1)) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) ,
  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 scheduled )
  **  ((error_address) # UChar  |-> 0)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (0) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (scheduled: bool) (tasks_waiting: Z) (PreH1 : ((unsigned_last_nbits (tasks_waiting) (32)) <> 1)) (PreH2 : (option = 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X 0 0 scheduled )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (0) (0)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_entail_wit_35_5 := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 7 false )
  **  ((error_address) # UChar  |-> 7)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) ,
  (flag_del_source_after_restore environment critical sg caller mask view pointer option name before X pointer 7 false )
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State) ,
  “ (0 <= option) ” 
  &&  “ (option <= 255) ”
  &&  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (7)) X )
  **  (GlobalStrings LitMap )
  **  (F )
).

Definition OSFlagDel_return_wit_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (returned_2: TaskSuspendCaller) (current_2: UCOS2_Verify_State) (after_local_2: (Armv7aContinuation -> Assertion)) (error_2: Z) (pgrp_return: Z) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) ,
  (flag_del_source_return_cut environment critical after_local_2 sg caller returned_2 mask pointer view option name before current_2 (pair (pgrp_return) (error_2)) X )
  **  ((error_address) # UChar  |-> error_2)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pgrp_return) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_return_wit_2 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (returned_2: TaskSuspendCaller) (current_2: UCOS2_Verify_State) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) ,
  (flag_del_source_return_cut environment critical protected_local sg caller returned_2 mask pointer view option name before current_2 (pair (pointer) (1)) X )
  **  ((error_address) # UChar  |-> 1)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_return_wit_3 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) ,
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (1)) X )
  **  ((error_address) # UChar  |-> 1)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_return_wit_4 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) ,
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (15)) X )
  **  ((error_address) # UChar  |-> 15)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_return_wit_5 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) ,
  (flag_del_source_return_cut environment critical local sg caller caller mask pointer view option name before before (pair (pointer) (110)) X )
  **  ((error_address) # UChar  |-> 110)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  EX (after_local: (Armv7aContinuation -> Assertion))  (returned: TaskSuspendCaller)  (current: UCOS2_Verify_State)  (error: Z) ,
  (flag_del_source_return_cut environment critical after_local sg caller returned mask pointer view option name before current (pair (pointer) (error)) X )
  **  ((error_address) # UChar  |-> error)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (source: FlagDelSourceABI) (PreH1 : (0 <= opt_pre)) (PreH2 : (opt_pre <= 255)) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (0 >= 0)) (PreH5 : (pgrp_pre = pointer)) (PreH6 : (opt_pre = option)) (PreH7 : (perr_pre = error_address)) (PreH8 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH9 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH10 : (name = (LitMap (("?"%string))))) (PreH11 : (flag_del_build_context sg )) (PreH12 : (flag_del_stack_layout sg )) (PreH13 : (kernel_sched_ready_clients critical )) (PreH14 : (flag_del_argument sg pgrp_pre view before observed )) (PreH15 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (flag_del_source_public_entry source environment critical local sg caller mask before pgrp_pre view perr_pre F )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= opt_pre) ” 
  &&  “ (opt_pre <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pgrp_pre = pointer) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (perr_pre = error_address) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pgrp_pre view before observed ) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X ) ”
  &&  (flag_del_source_public_entry source environment critical local sg caller mask before pgrp_pre view perr_pre F )
  **  (GlobalStrings LitMap )
.

Definition OSFlagDel_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (flag_del_source_cut sg caller before )) (PreH3 : (0 <= opt_pre)) (PreH4 : (opt_pre <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pgrp_pre = pointer)) (PreH8 : (opt_pre = option)) (PreH9 : (perr_pre = error_address)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH12 : (name = (LitMap (("?"%string))))) (PreH13 : (flag_del_build_context sg )) (PreH14 : (flag_del_stack_layout sg )) (PreH15 : (kernel_sched_ready_clients critical )) (PreH16 : (flag_del_argument sg pgrp_pre view before observed )) (PreH17 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (flag_del_closed environment local sg caller mask before )
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  (flag_del_raw_type pgrp_pre view )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  (F )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSFlagDel_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pgrp_pre: Z) (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (pgrp_pre <> 0)) (PreH2 : (flag_del_source_cut sg caller before )) (PreH3 : (0 <= opt_pre)) (PreH4 : (opt_pre <= 255)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (pgrp_pre = pointer)) (PreH8 : (opt_pre = option)) (PreH9 : (perr_pre = error_address)) (PreH10 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH11 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH12 : (name = (LitMap (("?"%string))))) (PreH13 : (flag_del_build_context sg )) (PreH14 : (flag_del_stack_layout sg )) (PreH15 : (kernel_sched_ready_clients critical )) (PreH16 : (flag_del_argument sg pgrp_pre view before observed )) (PreH17 : (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X )) ,
  (flag_del_closed environment local sg caller mask before )
  **  (flag_del_raw_type pgrp_pre view )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
  **  (GlobalStrings LitMap )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pgrp_pre <> 0) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (0 <= opt_pre) ” 
  &&  “ (opt_pre <= 255) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (pgrp_pre = pointer) ” 
  &&  “ (opt_pre = option) ” 
  &&  “ (perr_pre = error_address) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pgrp_pre view before observed ) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pgrp_pre opt_pre name before X ) ”
  &&  (flag_del_closed environment local sg caller mask before )
  **  (flag_del_raw_type pgrp_pre view )
  **  ((perr_pre) # UChar  |->_)
  **  (F )
  **  (GlobalStrings LitMap )
.

Definition OSFlagDel_partial_solve_wit_2 := OSFlagDel_partial_solve_wit_2_pure -> OSFlagDel_partial_solve_wit_2_aux.

Definition OSFlagDel_partial_solve_wit_3_pure := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_source_cut sg caller before )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH12 : (pointer <> 0)) (PreH13 : ((os_sched_ints (before)) = 0)) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  (flag_del_type_cut environment local sg caller mask pointer view before observed )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (pointer <> 0) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ”
.

Definition OSFlagDel_partial_solve_wit_3_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_source_cut sg caller before )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) (PreH12 : (pointer <> 0)) (PreH13 : ((os_sched_ints (before)) = 0)) ,
  (flag_del_type_cut environment local sg caller mask pointer view before observed )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (pointer <> 0) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pointer option name before X ) ” 
  &&  “ (pointer <> 0) ” 
  &&  “ ((os_sched_ints (before)) = 0) ”
  &&  (flag_del_type_cut environment local sg caller mask pointer view before observed )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_3 := OSFlagDel_partial_solve_wit_3_pure -> OSFlagDel_partial_solve_wit_3_aux.

Definition OSFlagDel_partial_solve_wit_4_pure := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (pointer <> 0)) (PreH12 : ((os_sched_ints (before)) = 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  (flag_del_closed environment local sg caller mask before )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ”
.

Definition OSFlagDel_partial_solve_wit_4_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (pointer <> 0)) (PreH12 : ((os_sched_ints (before)) = 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) ,
  (flag_del_closed environment local sg caller mask before )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (pointer <> 0) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pointer option name before X ) ”
  &&  (flag_del_closed environment local sg caller mask before )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_4 := OSFlagDel_partial_solve_wit_4_pure -> OSFlagDel_partial_solve_wit_4_aux.

Definition OSFlagDel_partial_solve_wit_5 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (save_heap: model) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_cut sg caller before )) (PreH11 : (pointer <> 0)) (PreH12 : ((os_sched_ints (before)) = 0)) (PreH13 : ((flagImageType (observed)) = 5)) (PreH14 : (flag_del_safe environment critical sg caller mask view pointer option name before X )) ,
  (os_sched_active_heap_cut (flag_del_source_save_input (environment) (critical) (local) (sg) (caller) (mask) (before)) save_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_cut sg caller before ) ” 
  &&  “ (pointer <> 0) ” 
  &&  “ ((os_sched_ints (before)) = 0) ” 
  &&  “ ((flagImageType (observed)) = 5) ” 
  &&  “ (flag_del_safe environment critical sg caller mask view pointer option name before X ) ”
  &&  (os_sched_active_heap_cut (flag_del_source_save_input (environment) (critical) (local) (sg) (caller) (mask) (before)) save_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_6_pure := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH11 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH12 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active acquired false ) ”
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active acquired false ) ”
).

Definition OSFlagDel_partial_solve_wit_6_pure_split_goal_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active acquired false ) ”
.

Definition OSFlagDel_partial_solve_wit_6_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH11 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH12 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active acquired false ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_6 := OSFlagDel_partial_solve_wit_6_pure -> OSFlagDel_partial_solve_wit_6_aux.

Definition OSFlagDel_partial_solve_wit_7 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (0 <= option)) (PreH2 : (option <= 255)) (PreH3 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH5 : (name = (LitMap (("?"%string))))) (PreH6 : (flag_del_build_context sg )) (PreH7 : (flag_del_stack_layout sg )) (PreH8 : (kernel_sched_ready_clients critical )) (PreH9 : (flag_del_argument sg pointer view before observed )) (PreH10 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH11 : (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired )) (PreH12 : (flag_del_source_cut sg active acquired )) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 1 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_8_pure := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (view = (FlagQueryPool (id)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH14 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) false ) ”
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH14 : (view = (FlagQueryPool (id)))) (PreH15 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH16 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) false ) ”
).

Definition OSFlagDel_partial_solve_wit_8_pure_split_goal_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH14 : (view = (FlagQueryPool (id)))) (PreH15 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH16 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) false ) ”
.

Definition OSFlagDel_partial_solve_wit_8_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (view = (FlagQueryPool (id)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH14 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) false ) ” 
  &&  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ” 
  &&  “ (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_8 := OSFlagDel_partial_solve_wit_8_pure -> OSFlagDel_partial_solve_wit_8_aux.

Definition OSFlagDel_partial_solve_wit_9 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (view = (FlagQueryPool (id)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) (PreH14 : (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) )) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) ((flag_del_release_state (sg) (acquired) (id) (image) (name))) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 false (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ” 
  &&  “ (flag_del_source_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) ) ”
  &&  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) ((flag_del_release_state (sg) (acquired) (id) (image) ((LitMap (("?"%string)))))) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_10_pure := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH13 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active acquired false ) ”
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH14 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH15 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active acquired false ) ”
).

Definition OSFlagDel_partial_solve_wit_10_pure_split_goal_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 0)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH14 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH15 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active acquired false ) ”
.

Definition OSFlagDel_partial_solve_wit_10_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH13 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active acquired false ) ” 
  &&  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_10 := OSFlagDel_partial_solve_wit_10_pure -> OSFlagDel_partial_solve_wit_10_aux.

Definition OSFlagDel_partial_solve_wit_11 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option = 0)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired )) (PreH13 : (flag_del_source_cut sg active acquired )) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (option = 0) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 73 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_12_pure := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) (PreH17 : (flag_del_waiter_at current pnode waiter old )) (PreH18 : (flag_del_loan_origin current waiter original fragments )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode)
  **  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (pnode = pnode) ” 
  &&  “ (0 = 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (2 = (encode_pend_status (PendAbort))) ”
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 1)) (PreH4 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH5 : (0 <= option)) (PreH6 : (option <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH9 : (name = (LitMap (("?"%string))))) (PreH10 : (flag_del_build_context sg )) (PreH11 : (flag_del_stack_layout sg )) (PreH12 : (kernel_sched_ready_clients critical )) (PreH13 : (flag_del_argument sg pointer view before observed )) (PreH14 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH15 : (view = (FlagQueryPool (id)))) (PreH16 : (flag_del_acquired_group acquired id image order )) (PreH17 : (tasks_waiting = (flag_del_waiting (image)))) (PreH18 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) (PreH19 : (flag_del_waiter_at current pnode waiter old )) (PreH20 : (flag_del_loan_origin current waiter original fragments )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode)
  **  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (2 = (encode_pend_status (PendAbort))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
).

Definition OSFlagDel_partial_solve_wit_12_pure_split_goal_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 1)) (PreH4 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH5 : (0 <= option)) (PreH6 : (option <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH9 : (name = (LitMap (("?"%string))))) (PreH10 : (flag_del_build_context sg )) (PreH11 : (flag_del_stack_layout sg )) (PreH12 : (kernel_sched_ready_clients critical )) (PreH13 : (flag_del_argument sg pointer view before observed )) (PreH14 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH15 : (view = (FlagQueryPool (id)))) (PreH16 : (flag_del_acquired_group acquired id image order )) (PreH17 : (tasks_waiting = (flag_del_waiting (image)))) (PreH18 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) (PreH19 : (flag_del_waiter_at current pnode waiter old )) (PreH20 : (flag_del_loan_origin current waiter original fragments )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode)
  **  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (2 = (encode_pend_status (PendAbort))) ”
.

Definition OSFlagDel_partial_solve_wit_12_pure_split_goal_2 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 1)) (PreH4 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH5 : (0 <= option)) (PreH6 : (option <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH9 : (name = (LitMap (("?"%string))))) (PreH10 : (flag_del_build_context sg )) (PreH11 : (flag_del_stack_layout sg )) (PreH12 : (kernel_sched_ready_clients critical )) (PreH13 : (flag_del_argument sg pointer view before observed )) (PreH14 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH15 : (view = (FlagQueryPool (id)))) (PreH16 : (flag_del_acquired_group acquired id image order )) (PreH17 : (tasks_waiting = (flag_del_waiting (image)))) (PreH18 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) (PreH19 : (flag_del_waiter_at current pnode waiter old )) (PreH20 : (flag_del_loan_origin current waiter original fragments )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode)
  **  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OSFlagDel_partial_solve_wit_12_pure_split_goal_3 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 1)) (PreH4 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH5 : (0 <= option)) (PreH6 : (option <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH9 : (name = (LitMap (("?"%string))))) (PreH10 : (flag_del_build_context sg )) (PreH11 : (flag_del_stack_layout sg )) (PreH12 : (kernel_sched_ready_clients critical )) (PreH13 : (flag_del_argument sg pointer view before observed )) (PreH14 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH15 : (view = (FlagQueryPool (id)))) (PreH16 : (flag_del_acquired_group acquired id image order )) (PreH17 : (tasks_waiting = (flag_del_waiting (image)))) (PreH18 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) (PreH19 : (flag_del_waiter_at current pnode waiter old )) (PreH20 : (flag_del_loan_origin current waiter original fragments )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode)
  **  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OSFlagDel_partial_solve_wit_12_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (current: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (order: (@list Z)) (visited: (@list Z)) (remaining: (@list Z)) (now_local: (Armv7aContinuation -> Assertion)) (waiter: FlagWaiterState) (old: TaskAbstractState) (original: TaskStackLease) (fragments: TaskStackFragments) (cpu_sr: Z) (tasks_waiting: Z) (pnode: Z) (PreH1 : (option = 1)) (PreH2 : (flag_del_local_prefix sg visited acquired protected_local current now_local )) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (view = (FlagQueryPool (id)))) (PreH14 : (flag_del_acquired_group acquired id image order )) (PreH15 : (tasks_waiting = (flag_del_waiting (image)))) (PreH16 : (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode )) (PreH17 : (flag_del_waiter_at current pnode waiter old )) (PreH18 : (flag_del_loan_origin current waiter original fragments )) ,
  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (pnode = pnode) ” 
  &&  “ (0 = 0) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (2 = (encode_pend_status (PendAbort))) ” 
  &&  “ (option = 1) ” 
  &&  “ (flag_del_local_prefix sg visited acquired protected_local current now_local ) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (view = (FlagQueryPool (id))) ” 
  &&  “ (flag_del_acquired_group acquired id image order ) ” 
  &&  “ (tasks_waiting = (flag_del_waiting (image))) ” 
  &&  “ (flag_del_source_loop_facts sg active acquired id order visited remaining current pnode ) ” 
  &&  “ (flag_del_waiter_at current pnode waiter old ) ” 
  &&  “ (flag_del_loan_origin current waiter original fragments ) ”
  &&  (flag_task_rdy_fields_pre sg current pnode waiter old 0 )
  **  (F )
  **  (flag_del_iteration_frame environment critical now_local sg active cpu_sr acquired current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
.

Definition OSFlagDel_partial_solve_wit_12 := OSFlagDel_partial_solve_wit_12_pure -> OSFlagDel_partial_solve_wit_12_aux.

Definition OSFlagDel_partial_solve_wit_13_pure := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled: bool) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released )) (PreH14 : (flag_del_source_cut sg active released )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active released (flag_del_schedule_bit (tasks_waiting)) ) ” 
  &&  “ (flag_del_source_restore_cut sg active released scheduled ) ”
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled: bool) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 1)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH14 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) (PreH15 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released )) (PreH16 : (flag_del_source_cut sg active released )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active released scheduled ) ” 
  &&  “ (flag_del_source_restore_cut sg active released scheduled ) ”
).

Definition OSFlagDel_partial_solve_wit_13_pure_split_goal_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled: bool) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 1)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH14 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) (PreH15 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released )) (PreH16 : (flag_del_source_cut sg active released )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active released scheduled ) ”
.

Definition OSFlagDel_partial_solve_wit_13_pure_split_goal_2 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled: bool) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option = 1)) (PreH4 : (0 <= option)) (PreH5 : (option <= 255)) (PreH6 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH8 : (name = (LitMap (("?"%string))))) (PreH9 : (flag_del_build_context sg )) (PreH10 : (flag_del_stack_layout sg )) (PreH11 : (kernel_sched_ready_clients critical )) (PreH12 : (flag_del_argument sg pointer view before observed )) (PreH13 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH14 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) (PreH15 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released )) (PreH16 : (flag_del_source_cut sg active released )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_waiting)
  **  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active released scheduled ) ”
.

Definition OSFlagDel_partial_solve_wit_13_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled: bool) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released )) (PreH14 : (flag_del_source_cut sg active released )) ,
  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active released (flag_del_schedule_bit (tasks_waiting)) ) ” 
  &&  “ (flag_del_source_restore_cut sg active released scheduled ) ” 
  &&  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (scheduled = (flag_del_schedule_bit (tasks_waiting))) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released ) ” 
  &&  “ (flag_del_source_cut sg active released ) ”
  &&  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_13 := OSFlagDel_partial_solve_wit_13_pure -> OSFlagDel_partial_solve_wit_13_aux.

Definition OSFlagDel_partial_solve_wit_14 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (tasks_waiting: Z) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (scheduled: bool) (restore_heap: model) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH12 : (scheduled = (flag_del_schedule_bit (tasks_waiting)))) (PreH13 : (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released )) (PreH14 : (flag_del_source_cut sg active released )) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (now_local) (sg) (active) (cpu_sr) (acquired) (released) ((flag_del_schedule_bit (tasks_waiting)))) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (scheduled = (flag_del_schedule_bit (tasks_waiting))) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired 0 0 scheduled released ) ” 
  &&  “ (flag_del_source_cut sg active released ) ”
  &&  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (now_local) (sg) (active) (cpu_sr) (acquired) (released) ((flag_del_schedule_bit (tasks_waiting)))) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_15_pure := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (context: OsSchedCallContext) (current: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current )) (PreH12 : (flag_del_scheduler_safe environment critical sg context mask current 0 0 X )) (PreH13 : (flag_del_same_task_call context caller )) (PreH14 : (os_sched_active_local_stable (flag_del_source_active (sg)) )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  (os_sched_active_call_pre environment now_local (flag_del_source_active (sg)) sg context mask current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable (flag_del_source_active (sg)) ) ”
.

Definition OSFlagDel_partial_solve_wit_15_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (context: OsSchedCallContext) (current: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (PreH1 : (option = 1)) (PreH2 : (0 <= option)) (PreH3 : (option <= 255)) (PreH4 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH5 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH6 : (name = (LitMap (("?"%string))))) (PreH7 : (flag_del_build_context sg )) (PreH8 : (flag_del_stack_layout sg )) (PreH9 : (kernel_sched_ready_clients critical )) (PreH10 : (flag_del_argument sg pointer view before observed )) (PreH11 : (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current )) (PreH12 : (flag_del_scheduler_safe environment critical sg context mask current 0 0 X )) (PreH13 : (flag_del_same_task_call context caller )) (PreH14 : (os_sched_active_local_stable (flag_del_source_active (sg)) )) ,
  (os_sched_active_call_pre environment now_local (flag_del_source_active (sg)) sg context mask current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (os_sched_active_local_stable (flag_del_source_active (sg)) ) ” 
  &&  “ (option = 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_prefix_to_scheduler environment critical sg caller mask view pointer option name before context current ) ” 
  &&  “ (flag_del_scheduler_safe environment critical sg context mask current 0 0 X ) ” 
  &&  “ (flag_del_same_task_call context caller ) ” 
  &&  “ (os_sched_active_local_stable (flag_del_source_active (sg)) ) ”
  &&  (os_sched_active_call_pre environment now_local (flag_del_source_active (sg)) sg context mask current )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_15 := OSFlagDel_partial_solve_wit_15_pure -> OSFlagDel_partial_solve_wit_15_aux.

Definition OSFlagDel_partial_solve_wit_16 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (restore_heap: model) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (option <> 0) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_17_pure := 
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active acquired false ) ”
) \/
(
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option <> 0)) (PreH4 : (option <> 1)) (PreH5 : (0 <= option)) (PreH6 : (option <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH9 : (name = (LitMap (("?"%string))))) (PreH10 : (flag_del_build_context sg )) (PreH11 : (flag_del_stack_layout sg )) (PreH12 : (kernel_sched_ready_clients critical )) (PreH13 : (flag_del_argument sg pointer view before observed )) (PreH14 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH15 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH16 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active acquired false ) ”
).

Definition OSFlagDel_partial_solve_wit_17_pure_split_goal_1 := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (cpu_sr <= UINT_MAX)) (PreH2 : (cpu_sr >= 0)) (PreH3 : (option <> 0)) (PreH4 : (option <> 1)) (PreH5 : (0 <= option)) (PreH6 : (option <= 255)) (PreH7 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH9 : (name = (LitMap (("?"%string))))) (PreH10 : (flag_del_build_context sg )) (PreH11 : (flag_del_stack_layout sg )) (PreH12 : (kernel_sched_ready_clients critical )) (PreH13 : (flag_del_argument sg pointer view before observed )) (PreH14 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH15 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH16 : (flag_del_source_cut sg active acquired )) ,
  ((( &( "opt" ) )) # UChar  |-> option)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pointer)
  **  ((( &( "perr" ) )) # Ptr  |-> error_address)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |->_)
  **  ((( &( "pgrp_return" ) )) # Ptr  |->_)
|--
  “ (flag_del_source_restore_cut sg active acquired false ) ”
.

Definition OSFlagDel_partial_solve_wit_17_aux := 
forall (F: Assertion) (LitMap: (string -> Z)) (X: ((Z * Z) -> (UCOS2_Verify_State -> Prop))) (error_address: Z) (option: Z) (pointer: Z) (name: Z) (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (cpu_sr: Z) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (PreH1 : (option <> 0)) (PreH2 : (option <> 1)) (PreH3 : (0 <= option)) (PreH4 : (option <= 255)) (PreH5 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg)))) (PreH7 : (name = (LitMap (("?"%string))))) (PreH8 : (flag_del_build_context sg )) (PreH9 : (flag_del_stack_layout sg )) (PreH10 : (kernel_sched_ready_clients critical )) (PreH11 : (flag_del_argument sg pointer view before observed )) (PreH12 : (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X )) (PreH13 : (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired )) (PreH14 : (flag_del_source_cut sg active acquired )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
|--
  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_source_restore_cut sg active acquired false ) ” 
  &&  “ (option <> 0) ” 
  &&  “ (option <> 1) ” 
  &&  “ (0 <= option) ” 
  &&  “ (option <= 255) ” 
  &&  “ (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (( &( "OSFlagFreeList" ) ) = (g_OSFlagFreeList (sg))) ” 
  &&  “ (name = (LitMap (("?"%string)))) ” 
  &&  “ (flag_del_build_context sg ) ” 
  &&  “ (flag_del_stack_layout sg ) ” 
  &&  “ (kernel_sched_ready_clients critical ) ” 
  &&  “ (flag_del_argument sg pointer view before observed ) ” 
  &&  “ (flag_del_source_prefix_facts environment critical sg caller mask view pointer option name before observed active cpu_sr acquired X ) ” 
  &&  “ (flag_del_protected_result sg view pointer option name acquired pointer 7 false acquired ) ” 
  &&  “ (flag_del_source_cut sg active acquired ) ”
  &&  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
  **  ((error_address) # UChar  |->_)
  **  (GlobalStrings LitMap )
  **  (F )
.

Definition OSFlagDel_partial_solve_wit_17 := OSFlagDel_partial_solve_wit_17_pure -> OSFlagDel_partial_solve_wit_17_aux.

Definition OSFlagDel_which_implies_wit_1 := 
(
forall (F: Assertion) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (source: FlagDelSourceABI) (perr: Z) (pgrp: Z) ,
  (flag_del_source_public_entry source environment critical local sg caller mask before pgrp view perr F )
|--
  “ (flag_del_source_cut sg caller before ) ”
  &&  (flag_del_closed environment local sg caller mask before )
  **  (flag_del_raw_type pgrp view )
  **  ((perr) # UChar  |->_)
  **  (F )
) \/
(
forall (F: Assertion) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (source: FlagDelSourceABI) (perr: Z) (pgrp: Z) ,
  (flag_del_source_public_entry source environment critical local sg caller mask before pgrp view perr F )
|--
  EX (x: Z) ,
  “ (flag_del_source_cut sg caller before ) ”
  &&  ((perr) # UChar  |-> x)
  **  (flag_del_closed environment local sg caller mask before )
  **  (flag_del_raw_type pgrp view )
  **  (F )
).

Definition OSFlagDel_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (flag_del_closed environment local sg caller mask before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (flag_del_closed environment local sg caller mask before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
).

Definition OSFlagDel_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (PreH1 : (os_sched_global_addresses sg ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) ,
  (flag_del_closed environment local sg caller mask before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_sched_ints (before)))
  **  (flag_del_nesting_frame environment local sg caller mask before )
.

Definition OSFlagDel_which_implies_wit_3 := 
(
forall (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pgrp: Z) (PreH1 : (pgrp <> 0)) (PreH2 : (flag_del_argument sg pgrp view before observed )) ,
  (flag_del_type_cut environment local sg caller mask pgrp view before observed )
|--
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pgrp view before observed )
) \/
(
forall (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pgrp: Z) (PreH1 : (pgrp <> 0)) (PreH2 : (flag_del_argument sg pgrp view before observed )) ,
  (flag_del_type_cut environment local sg caller mask pgrp view before observed )
|--
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pgrp view before observed )
).

Definition OSFlagDel_which_implies_wit_3_split_goal_spatial := 
forall (observed: FlagGroupImage) (before: UCOS2_Verify_State) (view: FlagQueryView) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (environment: TaskStackCallEnvironment) (pgrp: Z) (PreH1 : (pgrp <> 0)) (PreH2 : (flag_del_argument sg pgrp view before observed )) ,
  (flag_del_type_cut environment local sg caller mask pgrp view before observed )
|--
  ((&((pgrp)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> (flagImageType (observed)))
  **  (flag_del_type_read_frame environment local sg caller mask pgrp view before observed )
.

Definition OSFlagDel_which_implies_wit_4 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_cut sg caller before )) ,
  (flag_del_closed environment local sg caller mask before )
|--
  EX (save_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_save_input (environment) (critical) (local) (sg) (caller) (mask) (before)) save_heap )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (caller: TaskSuspendCaller) (sg: StableGlobVars) (local: (Armv7aContinuation -> Assertion)) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_cut sg caller before )) ,
  (flag_del_closed environment local sg caller mask before )
|--
  EX (save_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_save_input (environment) (critical) (local) (sg) (caller) (mask) (before)) save_heap )
).

Definition OSFlagDel_which_implies_wit_5 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active acquired false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active acquired false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
).

Definition OSFlagDel_which_implies_wit_6 := 
(
forall (name: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) ((flag_del_release_state (sg) (acquired) (id) (image) (name))) (false)) restore_heap )
) \/
(
forall (name: Z) (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (id: Z) (image: FlagGroupImage) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active (flag_del_release_state (sg) (acquired) (id) (image) (name)) false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired (flag_del_release_state (sg) (acquired) (id) (image) (name)) )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) ((flag_del_release_state (sg) (acquired) (id) (image) (name))) (false)) restore_heap )
).

Definition OSFlagDel_which_implies_wit_7 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active acquired false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active acquired false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
).

Definition OSFlagDel_which_implies_wit_8 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active released (flag_del_schedule_bit (tasks_waiting)) )) ,
  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (now_local) (sg) (active) (cpu_sr) (acquired) (released) ((flag_del_schedule_bit (tasks_waiting)))) restore_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (released: UCOS2_Verify_State) (now_local: (Armv7aContinuation -> Assertion)) (tasks_waiting: Z) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active released (flag_del_schedule_bit (tasks_waiting)) )) ,
  (flag_del_masked environment critical now_local sg active cpu_sr acquired released )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (now_local) (sg) (active) (cpu_sr) (acquired) (released) ((flag_del_schedule_bit (tasks_waiting)))) restore_heap )
).

Definition OSFlagDel_which_implies_wit_9 := 
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active acquired false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
) \/
(
forall (sg: StableGlobVars) (critical: CriticalRegionResources) (environment: TaskStackCallEnvironment) (protected_local: (Armv7aContinuation -> Assertion)) (active: TaskSuspendCaller) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (flag_del_build_context sg )) (PreH2 : (flag_del_stack_layout sg )) (PreH3 : (kernel_sched_ready_clients critical )) (PreH4 : (flag_del_source_restore_cut sg active acquired false )) ,
  (flag_del_masked environment critical protected_local sg active cpu_sr acquired acquired )
|--
  EX (restore_heap: model) ,
  (os_sched_active_heap_cut (flag_del_source_restore_input (environment) (critical) (protected_local) (sg) (active) (cpu_sr) (acquired) (acquired) (false)) restore_heap )
).

Module Type VC_Correct.


Axiom proof_of_OSFlagDel_safety_wit_1 : OSFlagDel_safety_wit_1.
Axiom proof_of_OSFlagDel_safety_wit_2 : OSFlagDel_safety_wit_2.
Axiom proof_of_OSFlagDel_safety_wit_3 : OSFlagDel_safety_wit_3.
Axiom proof_of_OSFlagDel_safety_wit_4 : OSFlagDel_safety_wit_4.
Axiom proof_of_OSFlagDel_safety_wit_5 : OSFlagDel_safety_wit_5.
Axiom proof_of_OSFlagDel_safety_wit_6 : OSFlagDel_safety_wit_6.
Axiom proof_of_OSFlagDel_safety_wit_7 : OSFlagDel_safety_wit_7.
Axiom proof_of_OSFlagDel_safety_wit_8 : OSFlagDel_safety_wit_8.
Axiom proof_of_OSFlagDel_safety_wit_9 : OSFlagDel_safety_wit_9.
Axiom proof_of_OSFlagDel_safety_wit_10 : OSFlagDel_safety_wit_10.
Axiom proof_of_OSFlagDel_safety_wit_11 : OSFlagDel_safety_wit_11.
Axiom proof_of_OSFlagDel_entail_wit_1 : OSFlagDel_entail_wit_1.
Axiom proof_of_OSFlagDel_entail_wit_2 : OSFlagDel_entail_wit_2.
Axiom proof_of_OSFlagDel_entail_wit_3 : OSFlagDel_entail_wit_3.
Axiom proof_of_OSFlagDel_entail_wit_4 : OSFlagDel_entail_wit_4.
Axiom proof_of_OSFlagDel_entail_wit_5 : OSFlagDel_entail_wit_5.
Axiom proof_of_OSFlagDel_entail_wit_6 : OSFlagDel_entail_wit_6.
Axiom proof_of_OSFlagDel_entail_wit_7 : OSFlagDel_entail_wit_7.
Axiom proof_of_OSFlagDel_entail_wit_8 : OSFlagDel_entail_wit_8.
Axiom proof_of_OSFlagDel_entail_wit_9_1 : OSFlagDel_entail_wit_9_1.
Axiom proof_of_OSFlagDel_entail_wit_9_2 : OSFlagDel_entail_wit_9_2.
Axiom proof_of_OSFlagDel_entail_wit_10 : OSFlagDel_entail_wit_10.
Axiom proof_of_OSFlagDel_entail_wit_11 : OSFlagDel_entail_wit_11.
Axiom proof_of_OSFlagDel_entail_wit_12_1 : OSFlagDel_entail_wit_12_1.
Axiom proof_of_OSFlagDel_entail_wit_12_2 : OSFlagDel_entail_wit_12_2.
Axiom proof_of_OSFlagDel_entail_wit_12_3 : OSFlagDel_entail_wit_12_3.
Axiom proof_of_OSFlagDel_entail_wit_13 : OSFlagDel_entail_wit_13.
Axiom proof_of_OSFlagDel_entail_wit_14_1 : OSFlagDel_entail_wit_14_1.
Axiom proof_of_OSFlagDel_entail_wit_14_2 : OSFlagDel_entail_wit_14_2.
Axiom proof_of_OSFlagDel_entail_wit_15 : OSFlagDel_entail_wit_15.
Axiom proof_of_OSFlagDel_entail_wit_16 : OSFlagDel_entail_wit_16.
Axiom proof_of_OSFlagDel_entail_wit_17 : OSFlagDel_entail_wit_17.
Axiom proof_of_OSFlagDel_entail_wit_18 : OSFlagDel_entail_wit_18.
Axiom proof_of_OSFlagDel_entail_wit_19 : OSFlagDel_entail_wit_19.
Axiom proof_of_OSFlagDel_entail_wit_20 : OSFlagDel_entail_wit_20.
Axiom proof_of_OSFlagDel_entail_wit_21 : OSFlagDel_entail_wit_21.
Axiom proof_of_OSFlagDel_entail_wit_22 : OSFlagDel_entail_wit_22.
Axiom proof_of_OSFlagDel_entail_wit_23 : OSFlagDel_entail_wit_23.
Axiom proof_of_OSFlagDel_entail_wit_24 : OSFlagDel_entail_wit_24.
Axiom proof_of_OSFlagDel_entail_wit_25 : OSFlagDel_entail_wit_25.
Axiom proof_of_OSFlagDel_entail_wit_26 : OSFlagDel_entail_wit_26.
Axiom proof_of_OSFlagDel_entail_wit_27 : OSFlagDel_entail_wit_27.
Axiom proof_of_OSFlagDel_entail_wit_28 : OSFlagDel_entail_wit_28.
Axiom proof_of_OSFlagDel_entail_wit_29 : OSFlagDel_entail_wit_29.
Axiom proof_of_OSFlagDel_entail_wit_30 : OSFlagDel_entail_wit_30.
Axiom proof_of_OSFlagDel_entail_wit_31 : OSFlagDel_entail_wit_31.
Axiom proof_of_OSFlagDel_entail_wit_32 : OSFlagDel_entail_wit_32.
Axiom proof_of_OSFlagDel_entail_wit_33 : OSFlagDel_entail_wit_33.
Axiom proof_of_OSFlagDel_entail_wit_34 : OSFlagDel_entail_wit_34.
Axiom proof_of_OSFlagDel_entail_wit_35_1 : OSFlagDel_entail_wit_35_1.
Axiom proof_of_OSFlagDel_entail_wit_35_2 : OSFlagDel_entail_wit_35_2.
Axiom proof_of_OSFlagDel_entail_wit_35_3 : OSFlagDel_entail_wit_35_3.
Axiom proof_of_OSFlagDel_entail_wit_35_4 : OSFlagDel_entail_wit_35_4.
Axiom proof_of_OSFlagDel_entail_wit_35_5 : OSFlagDel_entail_wit_35_5.
Axiom proof_of_OSFlagDel_return_wit_1 : OSFlagDel_return_wit_1.
Axiom proof_of_OSFlagDel_return_wit_2 : OSFlagDel_return_wit_2.
Axiom proof_of_OSFlagDel_return_wit_3 : OSFlagDel_return_wit_3.
Axiom proof_of_OSFlagDel_return_wit_4 : OSFlagDel_return_wit_4.
Axiom proof_of_OSFlagDel_return_wit_5 : OSFlagDel_return_wit_5.
Axiom proof_of_OSFlagDel_partial_solve_wit_1 : OSFlagDel_partial_solve_wit_1.
Axiom proof_of_OSFlagDel_partial_solve_wit_2_pure : OSFlagDel_partial_solve_wit_2_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_2 : OSFlagDel_partial_solve_wit_2.
Axiom proof_of_OSFlagDel_partial_solve_wit_3_pure : OSFlagDel_partial_solve_wit_3_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_3 : OSFlagDel_partial_solve_wit_3.
Axiom proof_of_OSFlagDel_partial_solve_wit_4_pure : OSFlagDel_partial_solve_wit_4_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_4 : OSFlagDel_partial_solve_wit_4.
Axiom proof_of_OSFlagDel_partial_solve_wit_5 : OSFlagDel_partial_solve_wit_5.
Axiom proof_of_OSFlagDel_partial_solve_wit_6_pure : OSFlagDel_partial_solve_wit_6_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_6 : OSFlagDel_partial_solve_wit_6.
Axiom proof_of_OSFlagDel_partial_solve_wit_7 : OSFlagDel_partial_solve_wit_7.
Axiom proof_of_OSFlagDel_partial_solve_wit_8_pure : OSFlagDel_partial_solve_wit_8_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_8 : OSFlagDel_partial_solve_wit_8.
Axiom proof_of_OSFlagDel_partial_solve_wit_9 : OSFlagDel_partial_solve_wit_9.
Axiom proof_of_OSFlagDel_partial_solve_wit_10_pure : OSFlagDel_partial_solve_wit_10_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_10 : OSFlagDel_partial_solve_wit_10.
Axiom proof_of_OSFlagDel_partial_solve_wit_11 : OSFlagDel_partial_solve_wit_11.
Axiom proof_of_OSFlagDel_partial_solve_wit_12_pure : OSFlagDel_partial_solve_wit_12_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_12 : OSFlagDel_partial_solve_wit_12.
Axiom proof_of_OSFlagDel_partial_solve_wit_13_pure : OSFlagDel_partial_solve_wit_13_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_13 : OSFlagDel_partial_solve_wit_13.
Axiom proof_of_OSFlagDel_partial_solve_wit_14 : OSFlagDel_partial_solve_wit_14.
Axiom proof_of_OSFlagDel_partial_solve_wit_15_pure : OSFlagDel_partial_solve_wit_15_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_15 : OSFlagDel_partial_solve_wit_15.
Axiom proof_of_OSFlagDel_partial_solve_wit_16 : OSFlagDel_partial_solve_wit_16.
Axiom proof_of_OSFlagDel_partial_solve_wit_17_pure : OSFlagDel_partial_solve_wit_17_pure.
Axiom proof_of_OSFlagDel_partial_solve_wit_17 : OSFlagDel_partial_solve_wit_17.
Axiom proof_of_OSFlagDel_which_implies_wit_1 : OSFlagDel_which_implies_wit_1.
Axiom proof_of_OSFlagDel_which_implies_wit_2 : OSFlagDel_which_implies_wit_2.
Axiom proof_of_OSFlagDel_which_implies_wit_3 : OSFlagDel_which_implies_wit_3.
Axiom proof_of_OSFlagDel_which_implies_wit_4 : OSFlagDel_which_implies_wit_4.
Axiom proof_of_OSFlagDel_which_implies_wit_5 : OSFlagDel_which_implies_wit_5.
Axiom proof_of_OSFlagDel_which_implies_wit_6 : OSFlagDel_which_implies_wit_6.
Axiom proof_of_OSFlagDel_which_implies_wit_7 : OSFlagDel_which_implies_wit_7.
Axiom proof_of_OSFlagDel_which_implies_wit_8 : OSFlagDel_which_implies_wit_8.
Axiom proof_of_OSFlagDel_which_implies_wit_9 : OSFlagDel_which_implies_wit_9.

End VC_Correct.
