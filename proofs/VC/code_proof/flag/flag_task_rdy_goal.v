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
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope sac_scope.
Local Open Scope sac.

(*----- Function OS_FlagTaskRdy -----*)

Definition OS_FlagTaskRdy_entail_wit_1 := 
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH3 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH4 : (flag_task_rdy_domain sg s p w old bits )) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (flag_task_rdy_domain sg s p w old bits )) (PreH7 : (pnode_pre = p)) (PreH8 : (flags_rdy_pre = bits)) (PreH9 : (pend_stat_pre = (encode_pend_status (result)))) (PreH10 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH11 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (Z.land (encode_task_status ((stat (old)))) (unsigned_last_nbits ((Z.lnot 32)) (8))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ ((flag_task_rdy_status (old)) = (flag_task_rdy_status (old))) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
) \/
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH6 : (flag_task_rdy_domain sg s p w old bits )) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (pnode_pre = p)) (PreH10 : (flags_rdy_pre = bits)) (PreH11 : (pend_stat_pre = (encode_pend_status (result)))) (PreH12 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH13 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  TT && emp 
|--
  “ ((Z.land (encode_task_status ((stat (old)))) (unsigned_last_nbits ((Z.lnot 32)) (8))) = (flag_task_rdy_status (old))) ”
  &&  emp
).

Definition OS_FlagTaskRdy_entail_wit_1_split_goal_1 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH5 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH6 : (flag_task_rdy_domain sg s p w old bits )) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (pnode_pre = p)) (PreH10 : (flags_rdy_pre = bits)) (PreH11 : (pend_stat_pre = (encode_pend_status (result)))) (PreH12 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH13 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((Z.land (encode_task_status ((stat (old)))) (unsigned_last_nbits ((Z.lnot 32)) (8))) = (flag_task_rdy_status (old)))
.

Definition OS_FlagTaskRdy_entail_wit_2 := 
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (flag_task_rdy_domain sg s p w old bits )) (PreH13 : (pnode_pre = p)) (PreH14 : (flags_rdy_pre = bits)) (PreH15 : (pend_stat_pre = (encode_pend_status (result)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH17 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_task_rdy_ready_group (s)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (flag_task_rdy_ready_row (s) (old)))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (0 <= (flag_task_rdy_ready_group (s))) ” 
  &&  “ ((flag_task_rdy_ready_group (s)) < 256) ” 
  &&  “ (0 <= (flag_task_rdy_ready_row (s) (old))) ” 
  &&  “ ((flag_task_rdy_ready_row (s) (old)) < 256) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_task_rdy_ready_group (s)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (flag_task_rdy_ready_row (s) (old)))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
) \/
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (flag_task_rdy_domain sg s p w old bits )) (PreH13 : (pnode_pre = p)) (PreH14 : (flags_rdy_pre = bits)) (PreH15 : (pend_stat_pre = (encode_pend_status (result)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH17 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  TT && emp 
|--
  “ ((flag_task_rdy_ready_row (s) (old)) < 256) ” 
  &&  “ (0 <= (flag_task_rdy_ready_row (s) (old))) ” 
  &&  “ ((flag_task_rdy_ready_group (s)) < 256) ” 
  &&  “ (0 <= (flag_task_rdy_ready_group (s))) ”
  &&  emp
).

Definition OS_FlagTaskRdy_entail_wit_2_split_goal_1 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (flag_task_rdy_domain sg s p w old bits )) (PreH13 : (pnode_pre = p)) (PreH14 : (flags_rdy_pre = bits)) (PreH15 : (pend_stat_pre = (encode_pend_status (result)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH17 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((flag_task_rdy_ready_row (s) (old)) < 256)
.

Definition OS_FlagTaskRdy_entail_wit_2_split_goal_2 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (flag_task_rdy_domain sg s p w old bits )) (PreH13 : (pnode_pre = p)) (PreH14 : (flags_rdy_pre = bits)) (PreH15 : (pend_stat_pre = (encode_pend_status (result)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH17 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (0 <= (flag_task_rdy_ready_row (s) (old)))
.

Definition OS_FlagTaskRdy_entail_wit_2_split_goal_3 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (flag_task_rdy_domain sg s p w old bits )) (PreH13 : (pnode_pre = p)) (PreH14 : (flags_rdy_pre = bits)) (PreH15 : (pend_stat_pre = (encode_pend_status (result)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH17 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((flag_task_rdy_ready_group (s)) < 256)
.

Definition OS_FlagTaskRdy_entail_wit_2_split_goal_4 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH4 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH5 : (0 <= UINT_MAX)) (PreH6 : (0 >= 0)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH9 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (flag_task_rdy_domain sg s p w old bits )) (PreH13 : (pnode_pre = p)) (PreH14 : (flags_rdy_pre = bits)) (PreH15 : (pend_stat_pre = (encode_pend_status (result)))) (PreH16 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH17 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (0 <= (flag_task_rdy_ready_group (s)))
.

Definition OS_FlagTaskRdy_entail_wit_3_1 := 
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) = 0)) (PreH3 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH4 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH5 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH6 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH10 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (flag_task_rdy_domain sg s p w old bits )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (flag_task_rdy_domain sg s p w old bits )) (PreH18 : (flag_task_rdy_domain sg s p w old bits )) (PreH19 : (pnode_pre = p)) (PreH20 : (flags_rdy_pre = bits)) (PreH21 : (pend_stat_pre = (encode_pend_status (result)))) (PreH22 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH23 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (1 = (flag_task_rdy_return (old))) ”
  &&  ((( &( "flags_rdy" ) )) # UShort  |-> bits)
  **  ((( &( "pend_stat" ) )) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
) \/
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) = 0)) (PreH3 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH4 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH5 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH6 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH10 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (flag_task_rdy_domain sg s p w old bits )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (flag_task_rdy_domain sg s p w old bits )) (PreH18 : (flag_task_rdy_domain sg s p w old bits )) (PreH19 : (pnode_pre = p)) (PreH20 : (flags_rdy_pre = bits)) (PreH21 : (pend_stat_pre = (encode_pend_status (result)))) (PreH22 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH23 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  TT && emp 
|--
  “ (1 = (flag_task_rdy_return (old))) ”
  &&  emp
).

Definition OS_FlagTaskRdy_entail_wit_3_1_split_goal_1 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) = 0)) (PreH3 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH4 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH5 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH6 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH9 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH10 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH11 : (0 <= UINT_MAX)) (PreH12 : (0 >= 0)) (PreH13 : (flag_task_rdy_domain sg s p w old bits )) (PreH14 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH15 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (flag_task_rdy_domain sg s p w old bits )) (PreH18 : (flag_task_rdy_domain sg s p w old bits )) (PreH19 : (pnode_pre = p)) (PreH20 : (flags_rdy_pre = bits)) (PreH21 : (pend_stat_pre = (encode_pend_status (result)))) (PreH22 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH23 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (1 = (flag_task_rdy_return (old)))
.

Definition OS_FlagTaskRdy_entail_wit_3_2 := 
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) <> 0)) (PreH3 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (flag_task_rdy_domain sg s p w old bits )) (PreH7 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH8 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (pnode_pre = p)) (PreH13 : (flags_rdy_pre = bits)) (PreH14 : (pend_stat_pre = (encode_pend_status (result)))) (PreH15 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH16 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (0 = (flag_task_rdy_return (old))) ”
  &&  ((( &( "flags_rdy" ) )) # UShort  |-> bits)
  **  ((( &( "pend_stat" ) )) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
) \/
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) <> 0)) (PreH3 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (flag_task_rdy_domain sg s p w old bits )) (PreH7 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH8 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (pnode_pre = p)) (PreH13 : (flags_rdy_pre = bits)) (PreH14 : (pend_stat_pre = (encode_pend_status (result)))) (PreH15 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH16 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  TT && emp 
|--
  “ (0 = (flag_task_rdy_return (old))) ”
  &&  emp
).

Definition OS_FlagTaskRdy_entail_wit_3_2_split_goal_1 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) <> 0)) (PreH3 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0)) (PreH4 : (0 <= UINT_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (flag_task_rdy_domain sg s p w old bits )) (PreH7 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH8 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (pnode_pre = p)) (PreH13 : (flags_rdy_pre = bits)) (PreH14 : (pend_stat_pre = (encode_pend_status (result)))) (PreH15 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH16 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (0 = (flag_task_rdy_return (old)))
.

Definition OS_FlagTaskRdy_return_wit_1 := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (sched = (flag_task_rdy_return (old)))) ,
  (flag_task_rdy_post sg s p w bits result (flag_task_rdy_return (old)) )
  **  (F )
|--
  (flag_task_rdy_post sg s p w bits result sched )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_1 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pnode_pre = p)) (PreH2 : (flags_rdy_pre = bits)) (PreH3 : (pend_stat_pre = (encode_pend_status (result)))) (PreH4 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH5 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (flag_task_rdy_pre sg s p w old bits )
  **  (F )
|--
  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (flag_task_rdy_pre sg s p w old bits )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_2_pure := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (pnode_pre = p)) (PreH3 : (flags_rdy_pre = bits)) (PreH4 : (pend_stat_pre = (encode_pend_status (result)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode_pre)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_2_aux := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (pnode_pre = p)) (PreH3 : (flags_rdy_pre = bits)) (PreH4 : (pend_stat_pre = (encode_pend_status (result)))) (PreH5 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH6 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> pnode_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_2 := OS_FlagTaskRdy_partial_solve_wit_2_pure -> OS_FlagTaskRdy_partial_solve_wit_2_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_3_pure := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (pnode_pre = p)) (PreH4 : (flags_rdy_pre = bits)) (PreH5 : (pend_stat_pre = (encode_pend_status (result)))) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_3_aux := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (pnode_pre = p)) (PreH4 : (flags_rdy_pre = bits)) (PreH5 : (pend_stat_pre = (encode_pend_status (result)))) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_3 := OS_FlagTaskRdy_partial_solve_wit_3_pure -> OS_FlagTaskRdy_partial_solve_wit_3_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_4_pure := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (pnode_pre = p)) (PreH5 : (flags_rdy_pre = bits)) (PreH6 : (pend_stat_pre = (encode_pend_status (result)))) (PreH7 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_4_aux := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (pnode_pre = p)) (PreH5 : (flags_rdy_pre = bits)) (PreH6 : (pend_stat_pre = (encode_pend_status (result)))) (PreH7 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH8 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (flag_unlink_task_rep sg w old )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_4 := OS_FlagTaskRdy_partial_solve_wit_4_pure -> OS_FlagTaskRdy_partial_solve_wit_4_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_5_pure := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH2 : ((flag_task_rdy_status (old)) = (flag_task_rdy_status (old)))) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (0 >= 0)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (pnode_pre = p)) (PreH12 : (flags_rdy_pre = bits)) (PreH13 : (pend_stat_pre = (encode_pend_status (result)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |->_)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_5_aux := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH2 : ((flag_task_rdy_status (old)) = (flag_task_rdy_status (old)))) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (0 >= 0)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (pnode_pre = p)) (PreH12 : (flags_rdy_pre = bits)) (PreH13 : (pend_stat_pre = (encode_pend_status (result)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_5 := OS_FlagTaskRdy_partial_solve_wit_5_pure -> OS_FlagTaskRdy_partial_solve_wit_5_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_6_pure := 
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH2 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH3 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH4 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH14 : (flag_task_rdy_domain sg s p w old bits )) (PreH15 : (flag_task_rdy_domain sg s p w old bits )) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (pnode_pre = p)) (PreH18 : (flags_rdy_pre = bits)) (PreH19 : (pend_stat_pre = (encode_pend_status (result)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH21 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "sched" ) )) # UChar  |-> 1)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ ((flag_task_rdy_status (old)) = 0) ” 
  &&  “ ((Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old)))))) ” 
  &&  “ ((Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old)))))) ”
) \/
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH2 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH3 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH4 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH14 : (flag_task_rdy_domain sg s p w old bits )) (PreH15 : (flag_task_rdy_domain sg s p w old bits )) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (pnode_pre = p)) (PreH18 : (flags_rdy_pre = bits)) (PreH19 : (pend_stat_pre = (encode_pend_status (result)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH21 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "sched" ) )) # UChar  |-> 1)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ ((Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old)))))) ” 
  &&  “ ((Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old)))))) ” 
  &&  “ ((flag_task_rdy_status (old)) = 0) ”
).

Definition OS_FlagTaskRdy_partial_solve_wit_6_pure_split_goal_1 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH2 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH3 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH4 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH14 : (flag_task_rdy_domain sg s p w old bits )) (PreH15 : (flag_task_rdy_domain sg s p w old bits )) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (pnode_pre = p)) (PreH18 : (flags_rdy_pre = bits)) (PreH19 : (pend_stat_pre = (encode_pend_status (result)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH21 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "sched" ) )) # UChar  |-> 1)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ ((Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old)))))) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_6_pure_split_goal_2 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH2 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH3 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH4 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH14 : (flag_task_rdy_domain sg s p w old bits )) (PreH15 : (flag_task_rdy_domain sg s p w old bits )) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (pnode_pre = p)) (PreH18 : (flags_rdy_pre = bits)) (PreH19 : (pend_stat_pre = (encode_pend_status (result)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH21 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "sched" ) )) # UChar  |-> 1)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ ((Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old)))))) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_6_pure_split_goal_3 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH2 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH3 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH4 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH14 : (flag_task_rdy_domain sg s p w old bits )) (PreH15 : (flag_task_rdy_domain sg s p w old bits )) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (pnode_pre = p)) (PreH18 : (flags_rdy_pre = bits)) (PreH19 : (pend_stat_pre = (encode_pend_status (result)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH21 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  ((( &( "sched" ) )) # UChar  |-> 1)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ ((flag_task_rdy_status (old)) = 0) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_6_aux := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= (flag_task_rdy_ready_group (s)))) (PreH2 : ((flag_task_rdy_ready_group (s)) < 256)) (PreH3 : (0 <= (flag_task_rdy_ready_row (s) (old)))) (PreH4 : ((flag_task_rdy_ready_row (s) (old)) < 256)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH7 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) (PreH8 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0)) (PreH9 : (0 <= UINT_MAX)) (PreH10 : (0 >= 0)) (PreH11 : (flag_task_rdy_domain sg s p w old bits )) (PreH12 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH13 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH14 : (flag_task_rdy_domain sg s p w old bits )) (PreH15 : (flag_task_rdy_domain sg s p w old bits )) (PreH16 : (flag_task_rdy_domain sg s p w old bits )) (PreH17 : (pnode_pre = p)) (PreH18 : (flags_rdy_pre = bits)) (PreH19 : (pend_stat_pre = (encode_pend_status (result)))) (PreH20 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH21 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ ((flag_task_rdy_status (old)) = 0) ” 
  &&  “ ((Z.lor (flag_task_rdy_ready_group (s)) (unsigned_last_nbits ((tcb_bit_y_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old)))))) ” 
  &&  “ ((Z.lor (flag_task_rdy_ready_row (s) (old)) (unsigned_last_nbits ((tcb_bit_x_of_prio ((curPrio (old))))) (8))) = (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old)))))) ” 
  &&  “ (0 <= (flag_task_rdy_ready_group (s))) ” 
  &&  “ ((flag_task_rdy_ready_group (s)) < 256) ” 
  &&  “ (0 <= (flag_task_rdy_ready_row (s) (old))) ” 
  &&  “ ((flag_task_rdy_ready_row (s) (old)) < 256) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ” 
  &&  “ ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) = 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old))))))
  **  (flag_task_rdy_ready_frame sg s old )
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_6 := OS_FlagTaskRdy_partial_solve_wit_6_pure -> OS_FlagTaskRdy_partial_solve_wit_6_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_7_pure := 
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0)) (PreH2 : ((flag_task_rdy_status (old)) = (flag_task_rdy_status (old)))) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (0 >= 0)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (pnode_pre = p)) (PreH12 : (flags_rdy_pre = bits)) (PreH13 : (pend_stat_pre = (encode_pend_status (result)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |-> 0)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ ((flag_task_rdy_status (old)) <> 0) ”
) \/
(
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (flag_task_rdy_domain sg s p w old bits )) (PreH5 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH6 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (pnode_pre = p)) (PreH11 : (flags_rdy_pre = bits)) (PreH12 : (pend_stat_pre = (encode_pend_status (result)))) (PreH13 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH14 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |-> 0)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ ((flag_task_rdy_status (old)) <> 0) ”
).

Definition OS_FlagTaskRdy_partial_solve_wit_7_pure_split_goal_1 := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0)) (PreH2 : (0 <= UINT_MAX)) (PreH3 : (0 >= 0)) (PreH4 : (flag_task_rdy_domain sg s p w old bits )) (PreH5 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH6 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH7 : (flag_task_rdy_domain sg s p w old bits )) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (pnode_pre = p)) (PreH11 : (flags_rdy_pre = bits)) (PreH12 : (pend_stat_pre = (encode_pend_status (result)))) (PreH13 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH14 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((( &( "sched" ) )) # UChar  |-> 0)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> flags_rdy_pre)
  **  ((( &( "pend_stat" ) )) # UChar  |-> pend_stat_pre)
  **  (F )
|--
  “ ((flag_task_rdy_status (old)) <> 0) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_7_aux := 
forall (pend_stat_pre: Z) (flags_rdy_pre: Z) (pnode_pre: Z) (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0)) (PreH2 : ((flag_task_rdy_status (old)) = (flag_task_rdy_status (old)))) (PreH3 : (0 <= UINT_MAX)) (PreH4 : (0 >= 0)) (PreH5 : (flag_task_rdy_domain sg s p w old bits )) (PreH6 : (0 <= (tcb_y_of_prio ((curPrio (old)))))) (PreH7 : ((tcb_y_of_prio ((curPrio (old)))) < 8)) (PreH8 : (flag_task_rdy_domain sg s p w old bits )) (PreH9 : (flag_task_rdy_domain sg s p w old bits )) (PreH10 : (flag_task_rdy_domain sg s p w old bits )) (PreH11 : (pnode_pre = p)) (PreH12 : (flags_rdy_pre = bits)) (PreH13 : (pend_stat_pre = (encode_pend_status (result)))) (PreH14 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH15 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ ((flag_task_rdy_status (old)) <> 0) ” 
  &&  “ ((unsigned_last_nbits ((flag_task_rdy_status (old))) (32)) <> 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (pnode_pre = p) ” 
  &&  “ (flags_rdy_pre = bits) ” 
  &&  “ (pend_stat_pre = (encode_pend_status (result))) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> flags_rdy_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> pend_stat_pre)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_7 := OS_FlagTaskRdy_partial_solve_wit_7_pure -> OS_FlagTaskRdy_partial_solve_wit_7_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_8_pure := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (sched = (flag_task_rdy_return (old)))) ,
  ((( &( "sched" ) )) # UChar  |-> sched)
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> bits)
  **  ((( &( "pend_stat" ) )) # UChar  |-> (encode_pend_status (result)))
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_8_aux := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (sched = (flag_task_rdy_return (old)))) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (sched = (flag_task_rdy_return (old))) ”
  &&  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_8 := OS_FlagTaskRdy_partial_solve_wit_8_pure -> OS_FlagTaskRdy_partial_solve_wit_8_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_9_pure := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (sched = (flag_task_rdy_return (old)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
  **  ((( &( "sched" ) )) # UChar  |-> sched)
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> bits)
  **  ((( &( "pend_stat" ) )) # UChar  |-> (encode_pend_status (result)))
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_9_aux := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (sched = (flag_task_rdy_return (old)))) ,
  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_raw_rep sg (FlagState (s)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (sched = (flag_task_rdy_return (old))) ”
  &&  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_9 := OS_FlagTaskRdy_partial_solve_wit_9_pure -> OS_FlagTaskRdy_partial_solve_wit_9_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_10 := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (sched = (flag_task_rdy_return (old)))) ,
  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (sched = (flag_task_rdy_return (old))) ”
  &&  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
  **  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
.

Definition OS_FlagTaskRdy_partial_solve_wit_11_pure := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (sched = (flag_task_rdy_return (old)))) ,
  (flag_task_rdy_call_frame sg s w old bits result F )
  **  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((( &( "sched" ) )) # UChar  |-> sched)
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> bits)
  **  ((( &( "pend_stat" ) )) # UChar  |-> (encode_pend_status (result)))
|--
  “ (p = p) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_11_aux := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (sched = (flag_task_rdy_return (old)))) ,
  (flag_task_rdy_call_frame sg s w old bits result F )
  **  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
|--
  “ (p = p) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (sched = (flag_task_rdy_return (old))) ”
  &&  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_task_rdy_call_frame sg s w old bits result F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_11 := OS_FlagTaskRdy_partial_solve_wit_11_pure -> OS_FlagTaskRdy_partial_solve_wit_11_aux.

Definition OS_FlagTaskRdy_partial_solve_wit_12_pure := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (sched = (flag_task_rdy_return (old)))) ,
  (flag_unlink_post sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_task_rdy_call_frame sg s w old bits result F )
  **  ((( &( "ptcb" ) )) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  ((( &( "sched" ) )) # UChar  |-> sched)
  **  ((( &( "pnode" ) )) # Ptr  |-> p)
  **  ((( &( "flags_rdy" ) )) # UShort  |-> bits)
  **  ((( &( "pend_stat" ) )) # UChar  |-> (encode_pend_status (result)))
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
.

Definition OS_FlagTaskRdy_partial_solve_wit_12_aux := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (sched: Z) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (flag_task_rdy_domain sg s p w old bits )) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) (PreH4 : (sched = (flag_task_rdy_return (old)))) ,
  (flag_unlink_post sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_task_rdy_call_frame sg s w old bits result F )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (sched = (flag_task_rdy_return (old))) ”
  &&  (flag_unlink_post sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_task_rdy_call_frame sg s w old bits result F )
.

Definition OS_FlagTaskRdy_partial_solve_wit_12 := OS_FlagTaskRdy_partial_solve_wit_12_pure -> OS_FlagTaskRdy_partial_solve_wit_12_aux.

Definition OS_FlagTaskRdy_which_implies_wit_1 := 
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (flag_task_rdy_pre sg s p w old bits )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
  &&  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
) \/
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (flag_task_rdy_pre sg s p w old bits )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
  &&  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
).

Definition OS_FlagTaskRdy_which_implies_wit_1_split_goal_1 := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (flag_task_rdy_pre sg s p w old bits )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
.

Definition OS_FlagTaskRdy_which_implies_wit_1_split_goal_spatial := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (flag_task_rdy_pre sg s p w old bits )
|--
  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w old )
  **  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
.

Definition OS_FlagTaskRdy_which_implies_wit_2 := 
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_raw_rep sg (FlagState (s)) )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
  &&  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
) \/
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_raw_rep sg (FlagState (s)) )
|--
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
).

Definition OS_FlagTaskRdy_which_implies_wit_2_split_goal_spatial := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_raw_rep sg (FlagState (s)) )
|--
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
.

Definition OS_FlagTaskRdy_which_implies_wit_3 := 
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
  &&  (flag_raw_rep sg (FlagState (s)) )
) \/
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
|--
  (flag_raw_rep sg (FlagState (s)) )
).

Definition OS_FlagTaskRdy_which_implies_wit_3_split_goal_spatial := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  ((&((p)  # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> (flag_unlink_tcb_addr (w)))
  **  (flag_task_rdy_node_frame sg (FlagState (s)) p w )
|--
  (flag_raw_rep sg (FlagState (s)) )
.

Definition OS_FlagTaskRdy_which_implies_wit_4 := 
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_task_rep sg w old )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ” 
  &&  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ”
  &&  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> (tcbFlagsRdy (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
) \/
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_task_rep sg w old )
|--
  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ”
  &&  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> (tcbFlagsRdy (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
).

Definition OS_FlagTaskRdy_which_implies_wit_4_split_goal_1 := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_task_rep sg w old )
|--
  “ ((tcb_y_of_prio ((curPrio (old)))) < 8) ”
.

Definition OS_FlagTaskRdy_which_implies_wit_4_split_goal_2 := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_task_rep sg w old )
|--
  “ (0 <= (tcb_y_of_prio ((curPrio (old))))) ”
.

Definition OS_FlagTaskRdy_which_implies_wit_4_split_goal_spatial := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_task_rep sg w old )
|--
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> (dly (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> (tcbFlagsRdy (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (encode_task_status ((stat (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status ((statPend (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
.

Definition OS_FlagTaskRdy_which_implies_wit_5 := 
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg))) ” 
  &&  “ (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg))) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_task_rdy_ready_group (s)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (flag_task_rdy_ready_row (s) (old)))
  **  (flag_task_rdy_ready_frame sg s old )
) \/
(
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
|--
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_task_rdy_ready_group (s)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (flag_task_rdy_ready_row (s) (old)))
  **  (flag_task_rdy_ready_frame sg s old )
).

Definition OS_FlagTaskRdy_which_implies_wit_5_split_goal_spatial := 
forall (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH3 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
|--
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (flag_task_rdy_ready_group (s)))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (flag_task_rdy_ready_row (s) (old)))
  **  (flag_task_rdy_ready_frame sg s old )
.

Definition OS_FlagTaskRdy_which_implies_wit_6 := 
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) = 0)) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH4 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old))))))
  **  (flag_task_rdy_ready_frame sg s old )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ ((flag_task_rdy_status (old)) = 0) ”
  &&  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
) \/
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) = 0)) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH4 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old))))))
  **  (flag_task_rdy_ready_frame sg s old )
|--
  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
).

Definition OS_FlagTaskRdy_which_implies_wit_6_split_goal_spatial := 
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) = 0)) (PreH3 : (( &( "OSRdyGrp" ) ) = (g_OSRdyGrp (sg)))) (PreH4 : (( &( "OSRdyTbl" ) ) = (g_OSRdyTbl (sg)))) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (flag_task_rdy_ready_group (s)) (tcb_bit_y_of_prio ((curPrio (old))))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((curPrio (old)))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (flag_task_rdy_ready_row (s) (old)) (tcb_bit_x_of_prio ((curPrio (old))))))
  **  (flag_task_rdy_ready_frame sg s old )
|--
  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
.

Definition OS_FlagTaskRdy_which_implies_wit_7 := 
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) <> 0)) ,
  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ” 
  &&  “ ((flag_task_rdy_status (old)) <> 0) ”
  &&  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
) \/
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) <> 0)) ,
  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
|--
  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
).

Definition OS_FlagTaskRdy_which_implies_wit_7_split_goal_spatial := 
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) (PreH2 : ((flag_task_rdy_status (old)) <> 0)) ,
  (sched_raw_rep sg (TskState (s)) (SchedState (s)) )
|--
  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
.

Definition OS_FlagTaskRdy_which_implies_wit_8 := 
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
  &&  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
) \/
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
|--
  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
).

Definition OS_FlagTaskRdy_which_implies_wit_8_split_goal_spatial := 
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (flag_task_rdy_domain sg s p w old bits )) ,
  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBDly")) # UInt  |-> 0)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBFlagsRdy")) # UShort  |-> bits)
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStat")) # UChar  |-> (flag_task_rdy_status (old)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBStatPend")) # UChar  |-> (encode_pend_status (result)))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((curPrio (old)))))
  **  ((&(((flag_unlink_tcb_addr (w)))  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((curPrio (old)))))
  **  (flag_task_rdy_tcb_frame (flag_unlink_tcb_addr (w)) (task_tcb64_image (sg) (old)) )
|--
  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
.

Definition OS_FlagTaskRdy_which_implies_wit_9 := 
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
|--
  “ (flag_task_rdy_domain sg s p w old bits ) ”
  &&  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
) \/
(
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
|--
  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
).

Definition OS_FlagTaskRdy_which_implies_wit_9_split_goal_spatial := 
forall (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_raw_rep sg (FlagState (s)) )
  **  (flag_unlink_task_rep sg w (flag_task_rdy_middle (old) (bits) (result)) )
|--
  (flag_unlink_pre sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
.

Definition OS_FlagTaskRdy_which_implies_wit_10 := 
(
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  (flag_task_rdy_call_frame sg s w old bits result F )
) \/
(
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  (flag_task_rdy_call_frame sg s w old bits result F )
).

Definition OS_FlagTaskRdy_which_implies_wit_10_split_goal_spatial := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (s: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (task_public_storage_without_task sg (TskState (s)) (flagTask (w)) )
  **  (sched_raw_rep sg (flag_task_rdy_after_tasks (s) (w) (old) (bits) (result)) (flag_task_rdy_after_sched (sg) (s) (w) (old) (bits) (result)) )
  **  (F )
|--
  (flag_task_rdy_call_frame sg s w old bits result F )
.

Definition OS_FlagTaskRdy_which_implies_wit_11 := 
(
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_post sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_task_rdy_call_frame sg s w old bits result F )
|--
  (flag_task_rdy_post sg s p w bits result (flag_task_rdy_return (old)) )
  **  (F )
) \/
(
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_post sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_task_rdy_call_frame sg s w old bits result F )
|--
  (flag_task_rdy_post sg s p w bits result (flag_task_rdy_return (old)) )
  **  (F )
).

Definition OS_FlagTaskRdy_which_implies_wit_11_split_goal_spatial := 
forall (F: Assertion) (result: PendStatus) (bits: Z) (old: TaskAbstractState) (w: FlagWaiterState) (p: Z) (s: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (flag_task_rdy_domain sg s p w old bits )) ,
  (flag_unlink_post sg (FlagState (s)) p w (flag_task_rdy_middle (old) (bits) (result)) )
  **  (flag_task_rdy_call_frame sg s w old bits result F )
|--
  (flag_task_rdy_post sg s p w bits result (flag_task_rdy_return (old)) )
  **  (F )
.

Module Type VC_Correct.


Axiom proof_of_OS_FlagTaskRdy_entail_wit_1 : OS_FlagTaskRdy_entail_wit_1.
Axiom proof_of_OS_FlagTaskRdy_entail_wit_2 : OS_FlagTaskRdy_entail_wit_2.
Axiom proof_of_OS_FlagTaskRdy_entail_wit_3_1 : OS_FlagTaskRdy_entail_wit_3_1.
Axiom proof_of_OS_FlagTaskRdy_entail_wit_3_2 : OS_FlagTaskRdy_entail_wit_3_2.
Axiom proof_of_OS_FlagTaskRdy_return_wit_1 : OS_FlagTaskRdy_return_wit_1.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_1 : OS_FlagTaskRdy_partial_solve_wit_1.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_2_pure : OS_FlagTaskRdy_partial_solve_wit_2_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_2 : OS_FlagTaskRdy_partial_solve_wit_2.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_3_pure : OS_FlagTaskRdy_partial_solve_wit_3_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_3 : OS_FlagTaskRdy_partial_solve_wit_3.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_4_pure : OS_FlagTaskRdy_partial_solve_wit_4_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_4 : OS_FlagTaskRdy_partial_solve_wit_4.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_5_pure : OS_FlagTaskRdy_partial_solve_wit_5_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_5 : OS_FlagTaskRdy_partial_solve_wit_5.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_6_pure : OS_FlagTaskRdy_partial_solve_wit_6_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_6 : OS_FlagTaskRdy_partial_solve_wit_6.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_7_pure : OS_FlagTaskRdy_partial_solve_wit_7_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_7 : OS_FlagTaskRdy_partial_solve_wit_7.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_8_pure : OS_FlagTaskRdy_partial_solve_wit_8_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_8 : OS_FlagTaskRdy_partial_solve_wit_8.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_9_pure : OS_FlagTaskRdy_partial_solve_wit_9_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_9 : OS_FlagTaskRdy_partial_solve_wit_9.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_10 : OS_FlagTaskRdy_partial_solve_wit_10.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_11_pure : OS_FlagTaskRdy_partial_solve_wit_11_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_11 : OS_FlagTaskRdy_partial_solve_wit_11.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_12_pure : OS_FlagTaskRdy_partial_solve_wit_12_pure.
Axiom proof_of_OS_FlagTaskRdy_partial_solve_wit_12 : OS_FlagTaskRdy_partial_solve_wit_12.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_1 : OS_FlagTaskRdy_which_implies_wit_1.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_2 : OS_FlagTaskRdy_which_implies_wit_2.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_3 : OS_FlagTaskRdy_which_implies_wit_3.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_4 : OS_FlagTaskRdy_which_implies_wit_4.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_5 : OS_FlagTaskRdy_which_implies_wit_5.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_6 : OS_FlagTaskRdy_which_implies_wit_6.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_7 : OS_FlagTaskRdy_which_implies_wit_7.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_8 : OS_FlagTaskRdy_which_implies_wit_8.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_9 : OS_FlagTaskRdy_which_implies_wit_9.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_10 : OS_FlagTaskRdy_which_implies_wit_10.
Axiom proof_of_OS_FlagTaskRdy_which_implies_wit_11 : OS_FlagTaskRdy_which_implies_wit_11.

End VC_Correct.
