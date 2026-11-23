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
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched Ucos2Verify.lib.flag Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope sac.

(*----- Function OS_FlagBlock -----*)

Definition OS_FlagBlock_safety_wit_1 := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_ranges s t )) (PreH3 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH4 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH7 : (pnode_pre = (flag_block_call_node (w)))) (PreH8 : (flags_pre = (flag_block_call_mask (w)))) (PreH9 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH10 : (timeout_pre = delay)) (PreH11 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH12 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH13 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> (flag_block_call_node (w)))
  **  ((( &( "flags" ) )) # UShort  |-> (flag_block_call_mask (w)))
  **  ((( &( "wait_type" ) )) # UChar  |-> (flag_block_call_mode (w)))
  **  ((( &( "timeout" ) )) # UInt  |-> delay)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |->_)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |->_)
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pnode_next" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagBlock_safety_wit_2 := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_ranges s t )) (PreH3 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH4 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH7 : (pnode_pre = (flag_block_call_node (w)))) (PreH8 : (flags_pre = (flag_block_call_mask (w)))) (PreH9 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH10 : (timeout_pre = delay)) (PreH11 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH12 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH13 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> (flag_block_call_node (w)))
  **  ((( &( "flags" ) )) # UShort  |-> (flag_block_call_mask (w)))
  **  ((( &( "wait_type" ) )) # UChar  |-> (flag_block_call_mode (w)))
  **  ((( &( "timeout" ) )) # UInt  |-> delay)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_block_call_head (v)))
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagBlock_entail_wit_1_1 := 
(
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_context sg s w t g v delay )) (PreH3 : ((flag_block_call_head (v)) <> 0)) (PreH4 : (flag_block_call_head_lookup s v previous )) (PreH5 : ((flag_block_call_head (v)) <> 0)) (PreH6 : (flag_block_call_context sg s w t g v delay )) (PreH7 : (flag_block_call_ranges s t )) (PreH8 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH9 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH10 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH11 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH12 : (pnode_pre = (flag_block_call_node (w)))) (PreH13 : (flags_pre = (flag_block_call_mask (w)))) (PreH14 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH15 : (timeout_pre = delay)) (PreH16 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH17 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH18 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_old_nodes sg s w v )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_node (w)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
) \/
(
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (delay <= UINT_MAX)) (PreH2 : (delay >= 0)) (PreH3 : (flag_block_call_context sg s w t g v delay )) (PreH4 : (flag_block_call_context sg s w t g v delay )) (PreH5 : ((flag_block_call_head (v)) <> 0)) (PreH6 : (flag_block_call_head_lookup s v previous )) (PreH7 : ((flag_block_call_head (v)) <> 0)) (PreH8 : (flag_block_call_context sg s w t g v delay )) (PreH9 : (flag_block_call_ranges s t )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH12 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH13 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH14 : (pnode_pre = (flag_block_call_node (w)))) (PreH15 : (flags_pre = (flag_block_call_mask (w)))) (PreH16 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH17 : (timeout_pre = delay)) (PreH18 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH19 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_old_nodes sg s w v )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_node (w)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
).

Definition OS_FlagBlock_entail_wit_1_1_split_goal_spatial := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (delay <= UINT_MAX)) (PreH2 : (delay >= 0)) (PreH3 : (flag_block_call_context sg s w t g v delay )) (PreH4 : (flag_block_call_context sg s w t g v delay )) (PreH5 : ((flag_block_call_head (v)) <> 0)) (PreH6 : (flag_block_call_head_lookup s v previous )) (PreH7 : ((flag_block_call_head (v)) <> 0)) (PreH8 : (flag_block_call_context sg s w t g v delay )) (PreH9 : (flag_block_call_ranges s t )) (PreH10 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH11 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH12 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH13 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH14 : (pnode_pre = (flag_block_call_node (w)))) (PreH15 : (flags_pre = (flag_block_call_mask (w)))) (PreH16 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH17 : (timeout_pre = delay)) (PreH18 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH19 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_old_nodes sg s w v )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_node (w)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
.

Definition OS_FlagBlock_entail_wit_1_2 := 
(
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((flag_block_call_head (v)) = 0)) (PreH2 : (flag_block_call_context sg s w t g v delay )) (PreH3 : (flag_block_call_ranges s t )) (PreH4 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH5 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH8 : (pnode_pre = (flag_block_call_node (w)))) (PreH9 : (flags_pre = (flag_block_call_mask (w)))) (PreH10 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH11 : (timeout_pre = delay)) (PreH12 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH13 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_node (w)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
) \/
(
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (delay <= UINT_MAX)) (PreH2 : (delay >= 0)) (PreH3 : ((flag_block_call_head (v)) = 0)) (PreH4 : (flag_block_call_context sg s w t g v delay )) (PreH5 : (flag_block_call_ranges s t )) (PreH6 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH10 : (pnode_pre = (flag_block_call_node (w)))) (PreH11 : (flags_pre = (flag_block_call_mask (w)))) (PreH12 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH13 : (timeout_pre = delay)) (PreH14 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH15 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_node (w)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
).

Definition OS_FlagBlock_entail_wit_1_2_split_goal_spatial := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (delay <= UINT_MAX)) (PreH2 : (delay >= 0)) (PreH3 : ((flag_block_call_head (v)) = 0)) (PreH4 : (flag_block_call_context sg s w t g v delay )) (PreH5 : (flag_block_call_ranges s t )) (PreH6 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH10 : (pnode_pre = (flag_block_call_node (w)))) (PreH11 : (flags_pre = (flag_block_call_mask (w)))) (PreH12 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH13 : (timeout_pre = delay)) (PreH14 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH15 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_node (w)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
.

Definition OS_FlagBlock_entail_wit_2_1 := 
(
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))) = 0)) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (flag_block_call_grp (s)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_y (t)))) (8))))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ”
  &&  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
) \/
(
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))) = 0)) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (flag_block_call_grp (s)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_y (t)))) (8))))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
  **  (F )
|--
  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
).

Definition OS_FlagBlock_entail_wit_2_1_split_goal_spatial := 
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))) = 0)) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land (flag_block_call_grp (s)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_y (t)))) (8))))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
  **  (F )
|--
  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
.

Definition OS_FlagBlock_entail_wit_2_2 := 
(
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))) <> 0)) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ”
  &&  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
) \/
(
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))) <> 0)) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
  **  (F )
|--
  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
).

Definition OS_FlagBlock_entail_wit_2_2_split_goal_spatial := 
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))) <> 0)) (PreH2 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (Z.land (flag_block_call_row (s) (t)) (unsigned_last_nbits ((Z.lnot (flag_block_call_bit_x (t)))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
  **  (F )
|--
  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
.

Definition OS_FlagBlock_return_wit_1 := 
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_ranges s t )) ,
  (flag_block_call_fields_post sg s w t delay )
  **  (F )
|--
  (flag_block_call_fields_post sg s w t delay )
  **  (F )
.

Definition OS_FlagBlock_partial_solve_wit_1_pure := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH2 : (pnode_pre = (flag_block_call_node (w)))) (PreH3 : (flags_pre = (flag_block_call_mask (w)))) (PreH4 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH5 : (timeout_pre = delay)) (PreH6 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pnode_next" ) )) # Ptr  |->_)
  **  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  (flag_block_call_fields_pre sg s w t g v delay )
  **  (F )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OS_FlagBlock_partial_solve_wit_1_aux := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH2 : (pnode_pre = (flag_block_call_node (w)))) (PreH3 : (flags_pre = (flag_block_call_mask (w)))) (PreH4 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH5 : (timeout_pre = delay)) (PreH6 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "pgrp" ) )) # Ptr  |-> pgrp_pre)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode_pre)
  **  ((( &( "flags" ) )) # UShort  |-> flags_pre)
  **  ((( &( "wait_type" ) )) # UChar  |-> wait_type_pre)
  **  ((( &( "timeout" ) )) # UInt  |-> timeout_pre)
  **  (flag_block_call_fields_pre sg s w t g v delay )
  **  (F )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (pgrp_pre = (flag_block_call_group (sg) (w))) ” 
  &&  “ (pnode_pre = (flag_block_call_node (w))) ” 
  &&  “ (flags_pre = (flag_block_call_mask (w))) ” 
  &&  “ (wait_type_pre = (flag_block_call_mode (w))) ” 
  &&  “ (timeout_pre = delay) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  (flag_block_call_fields_pre sg s w t g v delay )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> (flag_block_call_node (w)))
  **  ((( &( "flags" ) )) # UShort  |-> (flag_block_call_mask (w)))
  **  ((( &( "wait_type" ) )) # UChar  |-> (flag_block_call_mode (w)))
  **  ((( &( "timeout" ) )) # UInt  |-> delay)
  **  (F )
.

Definition OS_FlagBlock_partial_solve_wit_1 := OS_FlagBlock_partial_solve_wit_1_pure -> OS_FlagBlock_partial_solve_wit_1_aux.

Definition OS_FlagBlock_partial_solve_wit_2_pure := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((flag_block_call_head (v)) <> 0)) (PreH2 : (flag_block_call_context sg s w t g v delay )) (PreH3 : (flag_block_call_ranges s t )) (PreH4 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH5 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH8 : (pnode_pre = (flag_block_call_node (w)))) (PreH9 : (flags_pre = (flag_block_call_mask (w)))) (PreH10 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH11 : (timeout_pre = delay)) (PreH12 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH13 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> (flag_block_call_node (w)))
  **  ((( &( "flags" ) )) # UShort  |-> (flag_block_call_mask (w)))
  **  ((( &( "wait_type" ) )) # UChar  |-> (flag_block_call_mode (w)))
  **  ((( &( "timeout" ) )) # UInt  |-> delay)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_block_call_head (v)))
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ”
.

Definition OS_FlagBlock_partial_solve_wit_2_aux := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((flag_block_call_head (v)) <> 0)) (PreH2 : (flag_block_call_context sg s w t g v delay )) (PreH3 : (flag_block_call_ranges s t )) (PreH4 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH5 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH8 : (pnode_pre = (flag_block_call_node (w)))) (PreH9 : (flags_pre = (flag_block_call_mask (w)))) (PreH10 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH11 : (timeout_pre = delay)) (PreH12 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH13 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (pgrp_pre = (flag_block_call_group (sg) (w))) ” 
  &&  “ (pnode_pre = (flag_block_call_node (w))) ” 
  &&  “ (flags_pre = (flag_block_call_mask (w))) ” 
  &&  “ (wait_type_pre = (flag_block_call_mode (w))) ” 
  &&  “ (timeout_pre = delay) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  (flag_block_call_fields_nodes sg s )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_residual sg s w t v )
  **  (F )
.

Definition OS_FlagBlock_partial_solve_wit_2 := OS_FlagBlock_partial_solve_wit_2_pure -> OS_FlagBlock_partial_solve_wit_2_aux.

Definition OS_FlagBlock_partial_solve_wit_3_pure := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : ((flag_block_call_head (v)) <> 0)) (PreH3 : (flag_block_call_head_lookup s v previous )) (PreH4 : ((flag_block_call_head (v)) <> 0)) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH10 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH11 : (pnode_pre = (flag_block_call_node (w)))) (PreH12 : (flags_pre = (flag_block_call_mask (w)))) (PreH13 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH14 : (timeout_pre = delay)) (PreH15 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH16 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH17 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_block_call_node (w)))
  **  (flag_block_call_fields_head_frame sg s v previous )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> (flag_block_call_node (w)))
  **  ((( &( "flags" ) )) # UShort  |-> (flag_block_call_mask (w)))
  **  ((( &( "wait_type" ) )) # UChar  |-> (flag_block_call_mode (w)))
  **  ((( &( "timeout" ) )) # UInt  |-> delay)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_residual sg s w t v )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_block_call_head (v)))
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ (flag_block_call_head_lookup s v previous ) ”
.

Definition OS_FlagBlock_partial_solve_wit_3_aux := 
forall (timeout_pre: Z) (wait_type_pre: Z) (flags_pre: Z) (pnode_pre: Z) (pgrp_pre: Z) (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : ((flag_block_call_head (v)) <> 0)) (PreH3 : (flag_block_call_head_lookup s v previous )) (PreH4 : ((flag_block_call_head (v)) <> 0)) (PreH5 : (flag_block_call_context sg s w t g v delay )) (PreH6 : (flag_block_call_ranges s t )) (PreH7 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH9 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH10 : (pgrp_pre = (flag_block_call_group (sg) (w)))) (PreH11 : (pnode_pre = (flag_block_call_node (w)))) (PreH12 : (flags_pre = (flag_block_call_mask (w)))) (PreH13 : (wait_type_pre = (flag_block_call_mode (w)))) (PreH14 : (timeout_pre = delay)) (PreH15 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH16 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH17 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_block_call_node (w)))
  **  (flag_block_call_fields_head_frame sg s v previous )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_residual sg s w t v )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ (flag_block_call_head_lookup s v previous ) ” 
  &&  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ (flag_block_call_head_lookup s v previous ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (pgrp_pre = (flag_block_call_group (sg) (w))) ” 
  &&  “ (pnode_pre = (flag_block_call_node (w))) ” 
  &&  “ (flags_pre = (flag_block_call_mask (w))) ” 
  &&  “ (wait_type_pre = (flag_block_call_mode (w))) ” 
  &&  “ (timeout_pre = delay) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_block_call_node (w)))
  **  (flag_block_call_fields_head_frame sg s v previous )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.lor (unsigned_last_nbits ((flag_block_call_status (t))) (8)) 32))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> delay)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> (flag_block_call_node (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> (flag_block_call_mask (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> (flag_block_call_mode (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_block_call_head (v)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_residual sg s w t v )
  **  (F )
.

Definition OS_FlagBlock_partial_solve_wit_3 := OS_FlagBlock_partial_solve_wit_3_pure -> OS_FlagBlock_partial_solve_wit_3_aux.

Definition OS_FlagBlock_partial_solve_wit_4_pure := 
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_ranges s t )) (PreH3 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH4 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> (flag_block_call_node (w)))
  **  ((( &( "flags" ) )) # UShort  |-> (flag_block_call_mask (w)))
  **  ((( &( "wait_type" ) )) # UChar  |-> (flag_block_call_mode (w)))
  **  ((( &( "timeout" ) )) # UInt  |-> delay)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_block_call_head (v)))
  **  ((( &( "y" ) )) # UChar  |->_)
  **  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
.

Definition OS_FlagBlock_partial_solve_wit_4_aux := 
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_ranges s t )) (PreH3 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH4 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  (flag_block_call_fields_ready_stage sg s w t v delay )
  **  (F )
.

Definition OS_FlagBlock_partial_solve_wit_4 := OS_FlagBlock_partial_solve_wit_4_pure -> OS_FlagBlock_partial_solve_wit_4_aux.

Definition OS_FlagBlock_partial_solve_wit_5_pure := 
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_ranges s t )) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_block_call_group (sg) (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> (flag_block_call_node (w)))
  **  ((( &( "flags" ) )) # UShort  |-> (flag_block_call_mask (w)))
  **  ((( &( "wait_type" ) )) # UChar  |-> (flag_block_call_mode (w)))
  **  ((( &( "timeout" ) )) # UInt  |-> delay)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_block_call_head (v)))
  **  ((( &( "y" ) )) # UChar  |-> (flag_block_call_y (t)))
  **  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ”
.

Definition OS_FlagBlock_partial_solve_wit_5_aux := 
forall (F: Assertion) (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : (flag_block_call_ranges s t )) ,
  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ”
  &&  (flag_block_call_fields_written sg s w t v delay )
  **  (F )
.

Definition OS_FlagBlock_partial_solve_wit_5 := OS_FlagBlock_partial_solve_wit_5_pure -> OS_FlagBlock_partial_solve_wit_5_aux.

Definition OS_FlagBlock_which_implies_wit_1 := 
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_pre sg s w t g v delay )
|--
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_block_call_status (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (flag_block_call_pend (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (flag_block_call_delay (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |->_)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |->_)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |->_)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |->_)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |->_)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |->_)
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
) \/
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_pre sg s w t g v delay )
|--
  EX (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ (flag_block_call_ranges s t ) ” 
  &&  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> x_6)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> x_5)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> x_4)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> x_3)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> x_2)
  **  ((&(((flag_block_call_node (w)))  # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> x)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_block_call_status (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (flag_block_call_pend (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (flag_block_call_delay (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  ((&(((flag_block_call_group (sg) (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_block_call_head (v)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_nodes sg s )
  **  (flag_block_call_residual sg s w t v )
).

Definition OS_FlagBlock_which_implies_wit_2 := 
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : ((flag_block_call_head (v)) <> 0)) ,
  (flag_block_call_fields_nodes sg s )
|--
  EX (previous: FlagWaiterState) ,
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ (flag_block_call_head_lookup s v previous ) ”
  &&  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |->_)
  **  (flag_block_call_fields_head_frame sg s v previous )
) \/
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : ((flag_block_call_head (v)) <> 0)) ,
  (flag_block_call_fields_nodes sg s )
|--
  EX (x: Z)  (previous: FlagWaiterState) ,
  “ (flag_block_call_context sg s w t g v delay ) ” 
  &&  “ ((flag_block_call_head (v)) <> 0) ” 
  &&  “ (flag_block_call_head_lookup s v previous ) ”
  &&  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> x)
  **  (flag_block_call_fields_head_frame sg s v previous )
).

Definition OS_FlagBlock_which_implies_wit_3 := 
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : ((flag_block_call_head (v)) <> 0)) (PreH3 : (flag_block_call_head_lookup s v previous )) ,
  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_block_call_node (w)))
  **  (flag_block_call_fields_head_frame sg s v previous )
|--
  “ (flag_block_call_context sg s w t g v delay ) ”
  &&  (flag_block_call_fields_old_nodes sg s w v )
) \/
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : ((flag_block_call_head (v)) <> 0)) (PreH3 : (flag_block_call_head_lookup s v previous )) ,
  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_block_call_node (w)))
  **  (flag_block_call_fields_head_frame sg s v previous )
|--
  (flag_block_call_fields_old_nodes sg s w v )
).

Definition OS_FlagBlock_which_implies_wit_3_split_goal_spatial := 
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (previous: FlagWaiterState) (PreH1 : (flag_block_call_context sg s w t g v delay )) (PreH2 : ((flag_block_call_head (v)) <> 0)) (PreH3 : (flag_block_call_head_lookup s v previous )) ,
  ((&(((flag_block_call_head (v)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_block_call_node (w)))
  **  (flag_block_call_fields_head_frame sg s v previous )
|--
  (flag_block_call_fields_old_nodes sg s w v )
.

Definition OS_FlagBlock_which_implies_wit_4 := 
(
forall (delay: Z) (v: FlagGroupImage) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_ready_stage sg s w t v delay )
|--
  “ (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
) \/
(
forall (delay: Z) (v: FlagGroupImage) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_ready_stage sg s w t v delay )
|--
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
).

Definition OS_FlagBlock_which_implies_wit_4_split_goal_spatial := 
forall (delay: Z) (v: FlagGroupImage) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (( &( "OSTCBCur" ) ) = (g_OSTCBCur (sg)))) (PreH2 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) ,
  (flag_block_call_fields_ready_stage sg s w t v delay )
|--
  ((( &( "OSTCBCur" ) )) # Ptr  |-> (flag_block_call_tcb (sg) (w)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (flag_block_call_y (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (flag_block_call_bit_x (t)))
  **  ((&(((flag_block_call_tcb (sg) (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (flag_block_call_bit_y (t)))
  **  (((( &( "OSRdyTbl" ) ) + ((flag_block_call_y (t)) * sizeof(UCHAR)))) # UChar  |-> (flag_block_call_row (s) (t)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_block_call_grp (s)))
  **  (flag_block_call_fields_ready_frame sg s w t v delay )
.

Definition OS_FlagBlock_which_implies_wit_5 := 
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) ,
  (flag_block_call_fields_written sg s w t v delay )
|--
  (flag_block_call_fields_post sg s w t delay )
) \/
(
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) ,
  (flag_block_call_fields_written sg s w t v delay )
|--
  (flag_block_call_fields_post sg s w t delay )
).

Definition OS_FlagBlock_which_implies_wit_5_split_goal_spatial := 
forall (delay: Z) (v: FlagGroupImage) (g: FlagGroupState) (t: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_block_call_context sg s w t g v delay )) ,
  (flag_block_call_fields_written sg s w t v delay )
|--
  (flag_block_call_fields_post sg s w t delay )
.

Module Type VC_Correct.


Axiom proof_of_OS_FlagBlock_safety_wit_1 : OS_FlagBlock_safety_wit_1.
Axiom proof_of_OS_FlagBlock_safety_wit_2 : OS_FlagBlock_safety_wit_2.
Axiom proof_of_OS_FlagBlock_entail_wit_1_1 : OS_FlagBlock_entail_wit_1_1.
Axiom proof_of_OS_FlagBlock_entail_wit_1_2 : OS_FlagBlock_entail_wit_1_2.
Axiom proof_of_OS_FlagBlock_entail_wit_2_1 : OS_FlagBlock_entail_wit_2_1.
Axiom proof_of_OS_FlagBlock_entail_wit_2_2 : OS_FlagBlock_entail_wit_2_2.
Axiom proof_of_OS_FlagBlock_return_wit_1 : OS_FlagBlock_return_wit_1.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_1_pure : OS_FlagBlock_partial_solve_wit_1_pure.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_1 : OS_FlagBlock_partial_solve_wit_1.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_2_pure : OS_FlagBlock_partial_solve_wit_2_pure.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_2 : OS_FlagBlock_partial_solve_wit_2.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_3_pure : OS_FlagBlock_partial_solve_wit_3_pure.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_3 : OS_FlagBlock_partial_solve_wit_3.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_4_pure : OS_FlagBlock_partial_solve_wit_4_pure.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_4 : OS_FlagBlock_partial_solve_wit_4.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_5_pure : OS_FlagBlock_partial_solve_wit_5_pure.
Axiom proof_of_OS_FlagBlock_partial_solve_wit_5 : OS_FlagBlock_partial_solve_wit_5.
Axiom proof_of_OS_FlagBlock_which_implies_wit_1 : OS_FlagBlock_which_implies_wit_1.
Axiom proof_of_OS_FlagBlock_which_implies_wit_2 : OS_FlagBlock_which_implies_wit_2.
Axiom proof_of_OS_FlagBlock_which_implies_wit_3 : OS_FlagBlock_which_implies_wit_3.
Axiom proof_of_OS_FlagBlock_which_implies_wit_4 : OS_FlagBlock_which_implies_wit_4.
Axiom proof_of_OS_FlagBlock_which_implies_wit_5 : OS_FlagBlock_which_implies_wit_5.

End VC_Correct.
