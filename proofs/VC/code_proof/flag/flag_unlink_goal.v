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
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac.

(*----- Function OS_FlagUnlink -----*)

Definition OS_FlagUnlink_safety_wit_1 := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (pnode_pre = p)) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagUnlink_safety_wit_2 := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_prev (w)) = 0)) (PreH4 : (flag_unlink_group_lookup flags w image )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : ((flag_unlink_prev (w)) = 0)) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : (pnode_pre = p)) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_after_first_store_rep sg flags post w )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagUnlink_safety_wit_3 := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) (PreH4 : ((flag_unlink_next (w)) <> 0)) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_group_lookup flags w image )) (PreH9 : (flag_unlink_context sg flags p w t post )) (PreH10 : ((flag_unlink_prev (w)) = 0)) (PreH11 : (flag_unlink_context sg flags p w t post )) (PreH12 : (pnode_pre = p)) ,
  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> p)
  **  (flag_unlink_next_store_frame sg flags post w following )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagUnlink_safety_wit_4 := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_prev (w)) <> 0)) (PreH4 : (flag_unlink_prev_lookup flags w previous )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : ((flag_unlink_prev (w)) <> 0)) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : (pnode_pre = p)) ,
  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_after_first_store_rep sg flags post w )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagUnlink_safety_wit_5 := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> p)
  **  (flag_unlink_task_without_node sg w t )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagUnlink_safety_wit_6 := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> p)
  **  (flag_unlink_task_without_node sg w t )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagUnlink_entail_wit_1_1 := 
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) (PreH5 : ((flag_unlink_next (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : ((flag_unlink_prev (w)) = 0)) (PreH9 : (flag_unlink_group_lookup flags w image )) (PreH10 : (flag_unlink_context sg flags p w t post )) (PreH11 : ((flag_unlink_prev (w)) = 0)) (PreH12 : (flag_unlink_context sg flags p w t post )) (PreH13 : (pnode_pre = p)) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
) \/
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) (PreH5 : ((flag_unlink_next (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : ((flag_unlink_prev (w)) = 0)) (PreH9 : (flag_unlink_group_lookup flags w image )) (PreH10 : (flag_unlink_context sg flags p w t post )) (PreH11 : ((flag_unlink_prev (w)) = 0)) (PreH12 : (flag_unlink_context sg flags p w t post )) (PreH13 : (pnode_pre = p)) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
).

Definition OS_FlagUnlink_entail_wit_1_1_split_goal_spatial := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) (PreH5 : ((flag_unlink_next (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : ((flag_unlink_prev (w)) = 0)) (PreH9 : (flag_unlink_group_lookup flags w image )) (PreH10 : (flag_unlink_context sg flags p w t post )) (PreH11 : ((flag_unlink_prev (w)) = 0)) (PreH12 : (flag_unlink_context sg flags p w t post )) (PreH13 : (pnode_pre = p)) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_entail_wit_1_2 := 
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : ((flag_unlink_next (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) = 0)) (PreH5 : (flag_unlink_group_lookup flags w image )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
) \/
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : ((flag_unlink_next (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) = 0)) (PreH5 : (flag_unlink_group_lookup flags w image )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
).

Definition OS_FlagUnlink_entail_wit_1_2_split_goal_spatial := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : ((flag_unlink_next (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) = 0)) (PreH5 : (flag_unlink_group_lookup flags w image )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_entail_wit_2_1 := 
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) (PreH5 : ((flag_unlink_next (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : ((flag_unlink_prev (w)) <> 0)) (PreH9 : (flag_unlink_prev_lookup flags w previous )) (PreH10 : (flag_unlink_context sg flags p w t post )) (PreH11 : ((flag_unlink_prev (w)) <> 0)) (PreH12 : (flag_unlink_context sg flags p w t post )) (PreH13 : (pnode_pre = p)) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
) \/
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) (PreH5 : ((flag_unlink_next (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : ((flag_unlink_prev (w)) <> 0)) (PreH9 : (flag_unlink_prev_lookup flags w previous )) (PreH10 : (flag_unlink_context sg flags p w t post )) (PreH11 : ((flag_unlink_prev (w)) <> 0)) (PreH12 : (flag_unlink_context sg flags p w t post )) (PreH13 : (pnode_pre = p)) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
).

Definition OS_FlagUnlink_entail_wit_2_1_split_goal_spatial := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) (PreH5 : ((flag_unlink_next (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (flag_unlink_context sg flags p w t post )) (PreH8 : ((flag_unlink_prev (w)) <> 0)) (PreH9 : (flag_unlink_prev_lookup flags w previous )) (PreH10 : (flag_unlink_context sg flags p w t post )) (PreH11 : ((flag_unlink_prev (w)) <> 0)) (PreH12 : (flag_unlink_context sg flags p w t post )) (PreH13 : (pnode_pre = p)) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_entail_wit_2_2 := 
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : ((flag_unlink_next (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) <> 0)) (PreH5 : (flag_unlink_prev_lookup flags w previous )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) <> 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
) \/
(
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : ((flag_unlink_next (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) <> 0)) (PreH5 : (flag_unlink_prev_lookup flags w previous )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) <> 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
).

Definition OS_FlagUnlink_entail_wit_2_2_split_goal_spatial := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : ((flag_unlink_next (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) <> 0)) (PreH5 : (flag_unlink_prev_lookup flags w previous )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) <> 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_return_wit_1 := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_post sg flags p w t )
  **  (F )
|--
  (flag_unlink_post sg flags p w t )
  **  (F )
.

Definition OS_FlagUnlink_return_wit_2 := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_post sg flags p w t )
  **  (F )
|--
  (flag_unlink_post sg flags p w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_1 := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (PreH1 : (pnode_pre = p)) ,
  ((( &( "pnode" ) )) # Ptr  |-> pnode_pre)
  **  (flag_unlink_pre sg flags p w t )
  **  (F )
|--
  “ (pnode_pre = p) ”
  &&  (flag_unlink_pre sg flags p w t )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_2_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : ((flag_unlink_prev (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (pnode_pre = p)) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_2_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : ((flag_unlink_prev (w)) = 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (pnode_pre = p)) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_2 := OS_FlagUnlink_partial_solve_wit_2_pure -> OS_FlagUnlink_partial_solve_wit_2_aux.

Definition OS_FlagUnlink_partial_solve_wit_3_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (pnode_pre = p)) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg flags )
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ”
.

Definition OS_FlagUnlink_partial_solve_wit_3_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (pnode_pre = p)) ,
  (flag_raw_rep sg flags )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  (flag_raw_rep sg flags )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_3 := OS_FlagUnlink_partial_solve_wit_3_pure -> OS_FlagUnlink_partial_solve_wit_3_aux.

Definition OS_FlagUnlink_partial_solve_wit_4_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : (flag_unlink_group_lookup flags w image )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : ((flag_unlink_prev (w)) = 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (pnode_pre = p)) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_head_store_frame sg flags w image )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_group_lookup flags w image ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_4_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : (flag_unlink_group_lookup flags w image )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : ((flag_unlink_prev (w)) = 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (pnode_pre = p)) ,
  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_head_store_frame sg flags w image )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_group_lookup flags w image ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_group_lookup flags w image ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_head_store_frame sg flags w image )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_4 := OS_FlagUnlink_partial_solve_wit_4_pure -> OS_FlagUnlink_partial_solve_wit_4_aux.

Definition OS_FlagUnlink_partial_solve_wit_5_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : ((flag_unlink_next (w)) <> 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) = 0)) (PreH5 : (flag_unlink_group_lookup flags w image )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_after_first_store_rep sg flags post w )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ”
.

Definition OS_FlagUnlink_partial_solve_wit_5_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : ((flag_unlink_next (w)) <> 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) = 0)) (PreH5 : (flag_unlink_group_lookup flags w image )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_group_lookup flags w image ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_5 := OS_FlagUnlink_partial_solve_wit_5_pure -> OS_FlagUnlink_partial_solve_wit_5_aux.

Definition OS_FlagUnlink_partial_solve_wit_6_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) (PreH4 : ((flag_unlink_next (w)) <> 0)) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_group_lookup flags w image )) (PreH9 : (flag_unlink_context sg flags p w t post )) (PreH10 : ((flag_unlink_prev (w)) = 0)) (PreH11 : (flag_unlink_context sg flags p w t post )) (PreH12 : (pnode_pre = p)) ,
  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  (flag_unlink_next_store_frame sg flags post w following )
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_6_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) (PreH4 : ((flag_unlink_next (w)) <> 0)) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) = 0)) (PreH8 : (flag_unlink_group_lookup flags w image )) (PreH9 : (flag_unlink_context sg flags p w t post )) (PreH10 : ((flag_unlink_prev (w)) = 0)) (PreH11 : (flag_unlink_context sg flags p w t post )) (PreH12 : (pnode_pre = p)) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  (flag_unlink_next_store_frame sg flags post w following )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_group_lookup flags w image ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  (flag_unlink_next_store_frame sg flags post w following )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_6 := OS_FlagUnlink_partial_solve_wit_6_pure -> OS_FlagUnlink_partial_solve_wit_6_aux.

Definition OS_FlagUnlink_partial_solve_wit_7_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_7_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_7 := OS_FlagUnlink_partial_solve_wit_7_pure -> OS_FlagUnlink_partial_solve_wit_7_aux.

Definition OS_FlagUnlink_partial_solve_wit_8_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : ((flag_unlink_prev (w)) <> 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (pnode_pre = p)) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_8_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : ((flag_unlink_prev (w)) <> 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (pnode_pre = p)) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_8 := OS_FlagUnlink_partial_solve_wit_8_pure -> OS_FlagUnlink_partial_solve_wit_8_aux.

Definition OS_FlagUnlink_partial_solve_wit_9_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (pnode_pre = p)) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg flags )
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ”
.

Definition OS_FlagUnlink_partial_solve_wit_9_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (pnode_pre = p)) ,
  (flag_raw_rep sg flags )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  (flag_raw_rep sg flags )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_9 := OS_FlagUnlink_partial_solve_wit_9_pure -> OS_FlagUnlink_partial_solve_wit_9_aux.

Definition OS_FlagUnlink_partial_solve_wit_10_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) (PreH3 : (flag_unlink_prev_lookup flags w previous )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : ((flag_unlink_prev (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (pnode_pre = p)) ,
  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_prev_store_frame sg flags w previous )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_prev_lookup flags w previous ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_10_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) (PreH3 : (flag_unlink_prev_lookup flags w previous )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : ((flag_unlink_prev (w)) <> 0)) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : (pnode_pre = p)) ,
  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_prev_store_frame sg flags w previous )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_prev_lookup flags w previous ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_prev_lookup flags w previous ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_prev_store_frame sg flags w previous )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_10 := OS_FlagUnlink_partial_solve_wit_10_pure -> OS_FlagUnlink_partial_solve_wit_10_aux.

Definition OS_FlagUnlink_partial_solve_wit_11_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : ((flag_unlink_next (w)) <> 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) <> 0)) (PreH5 : (flag_unlink_prev_lookup flags w previous )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) <> 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_after_first_store_rep sg flags post w )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ”
.

Definition OS_FlagUnlink_partial_solve_wit_11_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : ((flag_unlink_next (w)) <> 0)) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : ((flag_unlink_prev (w)) <> 0)) (PreH5 : (flag_unlink_prev_lookup flags w previous )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) <> 0)) (PreH8 : (flag_unlink_context sg flags p w t post )) (PreH9 : (pnode_pre = p)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_prev_lookup flags w previous ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  (flag_unlink_after_first_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_11 := OS_FlagUnlink_partial_solve_wit_11_pure -> OS_FlagUnlink_partial_solve_wit_11_aux.

Definition OS_FlagUnlink_partial_solve_wit_12_pure := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) (PreH4 : ((flag_unlink_next (w)) <> 0)) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) <> 0)) (PreH8 : (flag_unlink_prev_lookup flags w previous )) (PreH9 : (flag_unlink_context sg flags p w t post )) (PreH10 : ((flag_unlink_prev (w)) <> 0)) (PreH11 : (flag_unlink_context sg flags p w t post )) (PreH12 : (pnode_pre = p)) ,
  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_next_store_frame sg flags post w following )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_task_rep sg w t )
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_12_aux := 
forall (pnode_pre: Z) (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) (PreH4 : ((flag_unlink_next (w)) <> 0)) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) (PreH7 : ((flag_unlink_prev (w)) <> 0)) (PreH8 : (flag_unlink_prev_lookup flags w previous )) (PreH9 : (flag_unlink_context sg flags p w t post )) (PreH10 : ((flag_unlink_prev (w)) <> 0)) (PreH11 : (flag_unlink_context sg flags p w t post )) (PreH12 : (pnode_pre = p)) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_next_store_frame sg flags post w following )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_prev_lookup flags w previous ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (pnode_pre = p) ”
  &&  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_next_store_frame sg flags post w following )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_12 := OS_FlagUnlink_partial_solve_wit_12_pure -> OS_FlagUnlink_partial_solve_wit_12_aux.

Definition OS_FlagUnlink_partial_solve_wit_13_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_13_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_after_next_store_rep sg flags post w )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_13 := OS_FlagUnlink_partial_solve_wit_13_pure -> OS_FlagUnlink_partial_solve_wit_13_aux.

Definition OS_FlagUnlink_partial_solve_wit_14_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_14_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_14 := OS_FlagUnlink_partial_solve_wit_14_pure -> OS_FlagUnlink_partial_solve_wit_14_aux.

Definition OS_FlagUnlink_partial_solve_wit_15_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_15_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_15 := OS_FlagUnlink_partial_solve_wit_15_pure -> OS_FlagUnlink_partial_solve_wit_15_aux.

Definition OS_FlagUnlink_partial_solve_wit_16_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_16_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_16 := OS_FlagUnlink_partial_solve_wit_16_pure -> OS_FlagUnlink_partial_solve_wit_16_aux.

Definition OS_FlagUnlink_partial_solve_wit_17_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_17_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_17 := OS_FlagUnlink_partial_solve_wit_17_pure -> OS_FlagUnlink_partial_solve_wit_17_aux.

Definition OS_FlagUnlink_partial_solve_wit_18_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_18_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_task_rep sg w t )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_18 := OS_FlagUnlink_partial_solve_wit_18_pure -> OS_FlagUnlink_partial_solve_wit_18_aux.

Definition OS_FlagUnlink_partial_solve_wit_19_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_19_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (flag_unlink_task_rep sg w t )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_task_rep sg w t )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_19 := OS_FlagUnlink_partial_solve_wit_19_pure -> OS_FlagUnlink_partial_solve_wit_19_aux.

Definition OS_FlagUnlink_partial_solve_wit_20_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_20_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_20 := OS_FlagUnlink_partial_solve_wit_20_pure -> OS_FlagUnlink_partial_solve_wit_20_aux.

Definition OS_FlagUnlink_partial_solve_wit_21_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_21_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_21 := OS_FlagUnlink_partial_solve_wit_21_pure -> OS_FlagUnlink_partial_solve_wit_21_aux.

Definition OS_FlagUnlink_partial_solve_wit_22_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |->_)
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_22_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_raw_rep sg post )
  **  (flag_unlink_loan sg w )
  **  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_22 := OS_FlagUnlink_partial_solve_wit_22_pure -> OS_FlagUnlink_partial_solve_wit_22_aux.

Definition OS_FlagUnlink_partial_solve_wit_23_pure := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  ((( &( "pnode_prev" ) )) # Ptr  |-> 0)
  **  ((( &( "pnode_next" ) )) # Ptr  |-> (flag_unlink_next (w)))
  **  ((( &( "pgrp" ) )) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
.

Definition OS_FlagUnlink_partial_solve_wit_23_aux := 
forall (F: Assertion) (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : (flag_unlink_context sg flags p w t post )) (PreH3 : (flag_unlink_context sg flags p w t post )) (PreH4 : (flag_unlink_context sg flags p w t post )) (PreH5 : (flag_unlink_context sg flags p w t post )) (PreH6 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
  **  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
  **  (F )
|--
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_raw_rep sg post )
  **  (flag_unlink_loan sg w )
  **  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
  **  (F )
.

Definition OS_FlagUnlink_partial_solve_wit_23 := OS_FlagUnlink_partial_solve_wit_23_pure -> OS_FlagUnlink_partial_solve_wit_23_aux.

Definition OS_FlagUnlink_which_implies_wit_1 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) ,
  (flag_unlink_pre sg flags p w t )
|--
  EX (post: GlobFlagState) ,
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) ,
  (flag_unlink_pre sg flags p w t )
|--
  EX (post: GlobFlagState) ,
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
  **  (flag_unlink_task_rep sg w t )
).

Definition OS_FlagUnlink_which_implies_wit_2 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_raw_rep sg flags )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
|--
  (flag_raw_rep sg flags )
).

Definition OS_FlagUnlink_which_implies_wit_2_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
|--
  (flag_raw_rep sg flags )
.

Definition OS_FlagUnlink_which_implies_wit_3 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) ,
  (flag_raw_rep sg flags )
|--
  EX (image: FlagGroupImage) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_group_lookup flags w image ) ”
  &&  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> p)
  **  (flag_unlink_head_store_frame sg flags w image )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) ,
  (flag_raw_rep sg flags )
|--
  EX (image: FlagGroupImage) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) = 0) ” 
  &&  “ (flag_unlink_group_lookup flags w image ) ”
  &&  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> p)
  **  (flag_unlink_head_store_frame sg flags w image )
).

Definition OS_FlagUnlink_which_implies_wit_4 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : (flag_unlink_group_lookup flags w image )) ,
  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_head_store_frame sg flags w image )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_after_first_store_rep sg flags post w )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : (flag_unlink_group_lookup flags w image )) ,
  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_head_store_frame sg flags w image )
|--
  (flag_unlink_after_first_store_rep sg flags post w )
).

Definition OS_FlagUnlink_which_implies_wit_4_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (image: FlagGroupImage) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : (flag_unlink_group_lookup flags w image )) ,
  ((&(((flag_unlink_group_addr (w)))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_head_store_frame sg flags w image )
|--
  (flag_unlink_after_first_store_rep sg flags post w )
.

Definition OS_FlagUnlink_which_implies_wit_5 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
|--
  EX (following: FlagWaiterState) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ”
  &&  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> p)
  **  (flag_unlink_next_store_frame sg flags post w following )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
|--
  EX (following: FlagWaiterState) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ”
  &&  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> p)
  **  (flag_unlink_next_store_frame sg flags post w following )
).

Definition OS_FlagUnlink_which_implies_wit_6 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  (flag_unlink_next_store_frame sg flags post w following )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  (flag_unlink_next_store_frame sg flags post w following )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
).

Definition OS_FlagUnlink_which_implies_wit_6_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) = 0)) (PreH3 : ((flag_unlink_next (w)) <> 0)) (PreH4 : (flag_unlink_next_lookup flags w following )) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> 0)
  **  (flag_unlink_next_store_frame sg flags post w following )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
.

Definition OS_FlagUnlink_which_implies_wit_7 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
).

Definition OS_FlagUnlink_which_implies_wit_7_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
.

Definition OS_FlagUnlink_which_implies_wit_8 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_raw_rep sg flags )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
|--
  (flag_raw_rep sg flags )
).

Definition OS_FlagUnlink_which_implies_wit_8_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> (flag_unlink_group_addr (w)))
  **  (flag_unlink_read_frame sg flags p w )
|--
  (flag_raw_rep sg flags )
.

Definition OS_FlagUnlink_which_implies_wit_9 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) ,
  (flag_raw_rep sg flags )
|--
  EX (previous: FlagWaiterState) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_prev_lookup flags w previous ) ”
  &&  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> p)
  **  (flag_unlink_prev_store_frame sg flags w previous )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) ,
  (flag_raw_rep sg flags )
|--
  EX (previous: FlagWaiterState) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_prev (w)) <> 0) ” 
  &&  “ (flag_unlink_prev_lookup flags w previous ) ”
  &&  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> p)
  **  (flag_unlink_prev_store_frame sg flags w previous )
).

Definition OS_FlagUnlink_which_implies_wit_10 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) (PreH3 : (flag_unlink_prev_lookup flags w previous )) ,
  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_prev_store_frame sg flags w previous )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_after_first_store_rep sg flags post w )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) (PreH3 : (flag_unlink_prev_lookup flags w previous )) ,
  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_prev_store_frame sg flags w previous )
|--
  (flag_unlink_after_first_store_rep sg flags post w )
).

Definition OS_FlagUnlink_which_implies_wit_10_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (previous: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_prev (w)) <> 0)) (PreH3 : (flag_unlink_prev_lookup flags w previous )) ,
  ((&(((flag_unlink_prev (w)))  # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> (flag_unlink_next (w)))
  **  (flag_unlink_prev_store_frame sg flags w previous )
|--
  (flag_unlink_after_first_store_rep sg flags post w )
.

Definition OS_FlagUnlink_which_implies_wit_11 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
|--
  EX (following: FlagWaiterState) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ”
  &&  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> p)
  **  (flag_unlink_next_store_frame sg flags post w following )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) ,
  (flag_unlink_after_first_store_rep sg flags post w )
|--
  EX (following: FlagWaiterState) ,
  “ (flag_unlink_context sg flags p w t post ) ” 
  &&  “ ((flag_unlink_next (w)) <> 0) ” 
  &&  “ (flag_unlink_next_lookup flags w following ) ”
  &&  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> p)
  **  (flag_unlink_next_store_frame sg flags post w following )
).

Definition OS_FlagUnlink_which_implies_wit_12 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_next_store_frame sg flags post w following )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_next_store_frame sg flags post w following )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
).

Definition OS_FlagUnlink_which_implies_wit_12_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (following: FlagWaiterState) (PreH1 : (flag_unlink_context sg flags p w t post )) (PreH2 : ((flag_unlink_next (w)) <> 0)) (PreH3 : (flag_unlink_next_lookup flags w following )) ,
  ((&(((flag_unlink_next (w)))  # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> (flag_unlink_prev (w)))
  **  (flag_unlink_next_store_frame sg flags post w following )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
.

Definition OS_FlagUnlink_which_implies_wit_13 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
).

Definition OS_FlagUnlink_which_implies_wit_13_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_after_next_store_rep sg flags post w )
|--
  (flag_unlink_loan sg w )
  **  (flag_raw_rep sg post )
.

Definition OS_FlagUnlink_which_implies_wit_14 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
|--
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
).

Definition OS_FlagUnlink_which_implies_wit_14_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_loan sg w )
|--
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
.

Definition OS_FlagUnlink_which_implies_wit_15 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_loan sg w )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
|--
  (flag_unlink_loan sg w )
).

Definition OS_FlagUnlink_which_implies_wit_15_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_node_without_tcb sg p w )
|--
  (flag_unlink_loan sg w )
.

Definition OS_FlagUnlink_which_implies_wit_16 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_task_rep sg w t )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> p)
  **  (flag_unlink_task_without_node sg w t )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_task_rep sg w t )
|--
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> p)
  **  (flag_unlink_task_without_node sg w t )
).

Definition OS_FlagUnlink_which_implies_wit_16_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_unlink_task_rep sg w t )
|--
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> p)
  **  (flag_unlink_task_without_node sg w t )
.

Definition OS_FlagUnlink_which_implies_wit_17 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
|--
  “ (flag_unlink_context sg flags p w t post ) ”
  &&  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
|--
  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
).

Definition OS_FlagUnlink_which_implies_wit_17_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagNode")) # Ptr  |-> 0)
  **  (flag_unlink_task_without_node sg w t )
|--
  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
.

Definition OS_FlagUnlink_which_implies_wit_18 := 
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_raw_rep sg post )
  **  (flag_unlink_loan sg w )
  **  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
|--
  (flag_unlink_post sg flags p w t )
) \/
(
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_raw_rep sg post )
  **  (flag_unlink_loan sg w )
  **  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
|--
  (flag_unlink_post sg flags p w t )
).

Definition OS_FlagUnlink_which_implies_wit_18_split_goal_spatial := 
forall (t: TaskAbstractState) (w: FlagWaiterState) (p: Z) (flags: GlobFlagState) (sg: StableGlobVars) (post: GlobFlagState) (PreH1 : (flag_unlink_context sg flags p w t post )) ,
  (flag_raw_rep sg post )
  **  (flag_unlink_loan sg w )
  **  (flag_unlink_task_rep sg w (task_set_flag_node (t) (0)) )
|--
  (flag_unlink_post sg flags p w t )
.

Module Type VC_Correct.


Axiom proof_of_OS_FlagUnlink_safety_wit_1 : OS_FlagUnlink_safety_wit_1.
Axiom proof_of_OS_FlagUnlink_safety_wit_2 : OS_FlagUnlink_safety_wit_2.
Axiom proof_of_OS_FlagUnlink_safety_wit_3 : OS_FlagUnlink_safety_wit_3.
Axiom proof_of_OS_FlagUnlink_safety_wit_4 : OS_FlagUnlink_safety_wit_4.
Axiom proof_of_OS_FlagUnlink_safety_wit_5 : OS_FlagUnlink_safety_wit_5.
Axiom proof_of_OS_FlagUnlink_safety_wit_6 : OS_FlagUnlink_safety_wit_6.
Axiom proof_of_OS_FlagUnlink_entail_wit_1_1 : OS_FlagUnlink_entail_wit_1_1.
Axiom proof_of_OS_FlagUnlink_entail_wit_1_2 : OS_FlagUnlink_entail_wit_1_2.
Axiom proof_of_OS_FlagUnlink_entail_wit_2_1 : OS_FlagUnlink_entail_wit_2_1.
Axiom proof_of_OS_FlagUnlink_entail_wit_2_2 : OS_FlagUnlink_entail_wit_2_2.
Axiom proof_of_OS_FlagUnlink_return_wit_1 : OS_FlagUnlink_return_wit_1.
Axiom proof_of_OS_FlagUnlink_return_wit_2 : OS_FlagUnlink_return_wit_2.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_1 : OS_FlagUnlink_partial_solve_wit_1.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_2_pure : OS_FlagUnlink_partial_solve_wit_2_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_2 : OS_FlagUnlink_partial_solve_wit_2.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_3_pure : OS_FlagUnlink_partial_solve_wit_3_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_3 : OS_FlagUnlink_partial_solve_wit_3.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_4_pure : OS_FlagUnlink_partial_solve_wit_4_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_4 : OS_FlagUnlink_partial_solve_wit_4.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_5_pure : OS_FlagUnlink_partial_solve_wit_5_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_5 : OS_FlagUnlink_partial_solve_wit_5.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_6_pure : OS_FlagUnlink_partial_solve_wit_6_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_6 : OS_FlagUnlink_partial_solve_wit_6.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_7_pure : OS_FlagUnlink_partial_solve_wit_7_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_7 : OS_FlagUnlink_partial_solve_wit_7.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_8_pure : OS_FlagUnlink_partial_solve_wit_8_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_8 : OS_FlagUnlink_partial_solve_wit_8.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_9_pure : OS_FlagUnlink_partial_solve_wit_9_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_9 : OS_FlagUnlink_partial_solve_wit_9.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_10_pure : OS_FlagUnlink_partial_solve_wit_10_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_10 : OS_FlagUnlink_partial_solve_wit_10.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_11_pure : OS_FlagUnlink_partial_solve_wit_11_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_11 : OS_FlagUnlink_partial_solve_wit_11.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_12_pure : OS_FlagUnlink_partial_solve_wit_12_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_12 : OS_FlagUnlink_partial_solve_wit_12.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_13_pure : OS_FlagUnlink_partial_solve_wit_13_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_13 : OS_FlagUnlink_partial_solve_wit_13.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_14_pure : OS_FlagUnlink_partial_solve_wit_14_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_14 : OS_FlagUnlink_partial_solve_wit_14.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_15_pure : OS_FlagUnlink_partial_solve_wit_15_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_15 : OS_FlagUnlink_partial_solve_wit_15.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_16_pure : OS_FlagUnlink_partial_solve_wit_16_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_16 : OS_FlagUnlink_partial_solve_wit_16.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_17_pure : OS_FlagUnlink_partial_solve_wit_17_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_17 : OS_FlagUnlink_partial_solve_wit_17.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_18_pure : OS_FlagUnlink_partial_solve_wit_18_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_18 : OS_FlagUnlink_partial_solve_wit_18.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_19_pure : OS_FlagUnlink_partial_solve_wit_19_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_19 : OS_FlagUnlink_partial_solve_wit_19.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_20_pure : OS_FlagUnlink_partial_solve_wit_20_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_20 : OS_FlagUnlink_partial_solve_wit_20.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_21_pure : OS_FlagUnlink_partial_solve_wit_21_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_21 : OS_FlagUnlink_partial_solve_wit_21.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_22_pure : OS_FlagUnlink_partial_solve_wit_22_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_22 : OS_FlagUnlink_partial_solve_wit_22.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_23_pure : OS_FlagUnlink_partial_solve_wit_23_pure.
Axiom proof_of_OS_FlagUnlink_partial_solve_wit_23 : OS_FlagUnlink_partial_solve_wit_23.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_1 : OS_FlagUnlink_which_implies_wit_1.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_2 : OS_FlagUnlink_which_implies_wit_2.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_3 : OS_FlagUnlink_which_implies_wit_3.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_4 : OS_FlagUnlink_which_implies_wit_4.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_5 : OS_FlagUnlink_which_implies_wit_5.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_6 : OS_FlagUnlink_which_implies_wit_6.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_7 : OS_FlagUnlink_which_implies_wit_7.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_8 : OS_FlagUnlink_which_implies_wit_8.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_9 : OS_FlagUnlink_which_implies_wit_9.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_10 : OS_FlagUnlink_which_implies_wit_10.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_11 : OS_FlagUnlink_which_implies_wit_11.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_12 : OS_FlagUnlink_which_implies_wit_12.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_13 : OS_FlagUnlink_which_implies_wit_13.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_14 : OS_FlagUnlink_which_implies_wit_14.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_15 : OS_FlagUnlink_which_implies_wit_15.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_16 : OS_FlagUnlink_which_implies_wit_16.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_17 : OS_FlagUnlink_which_implies_wit_17.
Axiom proof_of_OS_FlagUnlink_which_implies_wit_18 : OS_FlagUnlink_which_implies_wit_18.

End VC_Correct.
