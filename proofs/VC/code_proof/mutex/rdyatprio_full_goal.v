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
Import naive_C_Rules.
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
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_rdyatprio_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Local Open Scope sac.

(*----- Function OSMutex_RdyAtPrio_full -----*)

Definition OSMutex_RdyAtPrio_full_safety_wit_1_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_1_current_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_1_current_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (3 <= 31) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_1_current_owner_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= 3) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_2_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_2_current_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_2_current_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (3 <= 31) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_2_current_owner_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= 3) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (3 <= 31) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= 3) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_pre) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (3 <= 31) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= 3) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_5_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_5_current_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_5_current_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_6_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_6_current_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_6_current_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_7_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_7_noncurrent_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_7_noncurrent_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_8_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_8_noncurrent_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_8_noncurrent_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_9_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_9_current_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_9_current_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_10_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_10_current_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_10_current_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_11_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_11_noncurrent_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_11_noncurrent_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_12_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OSMutex_RdyAtPrio_full_safety_wit_12_noncurrent_owner_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_full_safety_wit_12_noncurrent_owner_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OSMutex_RdyAtPrio_full_return_wit_1_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
).

Definition OSMutex_RdyAtPrio_full_return_wit_2_noncurrent_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
).

Definition OSMutex_RdyAtPrio_full_return_wit_3_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
).

Definition OSMutex_RdyAtPrio_full_return_wit_4_current_owner := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (restore_mid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> pt)
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  EX (new_t: TaskAbstractState)  (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (OSMutex_RdyAtPrio_LastSeen (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) (return (tt)) X ) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (OSMutex_RdyAtPrio_guarantee (sg) (ptcb_pre) (prio_pre) (ls0) (ls_post)) )
  **  (InsideCritical sg ls0 )
  **  (OSMutex_RdyAtPrio_raw_stage sg ls0 tid old_t prio_in tcb_x_out tcb_y_out tcb_bitx_out tcb_bity_out rdy_grp_out rdyL_out prioL_out )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_ready_snapshot (sg) (ls0) (tid) (old_t) (prio_in) (ls_post) (rdy_grp_out) (rdyL_out)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_preservation (sg) (ls0) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (OSMutex_RdyAtPrio_conditional_cross (sg) (ls0) (restore_mid) (tid) (old_t) (prio_in) (ls_post)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls_post.(TskState) )) (tid) (new_t) (pt) (prio_in) (tcb_x_out) (tcb_y_out) (tcb_bitx_out) (tcb_bity_out)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls_post.(TskState) )) (prioL_out)) )
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_1_pure := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = prio_in)) (PreH2 : (pt = ptcb_pre)) (PreH3 : (pt <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH5 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH6 : (0 <= tcb_y_in)) (PreH7 : (tcb_y_in < 8)) (PreH8 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH9 : (tcb_x_out = (Z.land prio_in 7))) (PreH10 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH11 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH12 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH13 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH14 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH15 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH16 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH17 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (pt = pt) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_1_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = prio_in)) (PreH2 : (pt = ptcb_pre)) (PreH3 : (pt <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH5 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH6 : (0 <= tcb_y_in)) (PreH7 : (tcb_y_in < 8)) (PreH8 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH9 : (tcb_x_out = (Z.land prio_in 7))) (PreH10 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH11 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH12 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH13 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH14 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH15 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH16 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH17 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (pt = pt) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_1 := OSMutex_RdyAtPrio_full_partial_solve_wit_1_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_1_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_2_pure := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = prio_in)) (PreH2 : (pt = ptcb_pre)) (PreH3 : (pt <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH5 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH6 : (0 <= tcb_y_in)) (PreH7 : (tcb_y_in < 8)) (PreH8 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH9 : (tcb_x_out = (Z.land prio_in 7))) (PreH10 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH11 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH12 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH13 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH14 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH15 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH16 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH17 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcb_prio_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  (store_osrdytbl sg rdyL_in )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_2_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (prio_pre = prio_in)) (PreH2 : (pt = ptcb_pre)) (PreH3 : (pt <> 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH5 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH6 : (0 <= tcb_y_in)) (PreH7 : (tcb_y_in < 8)) (PreH8 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH9 : (tcb_x_out = (Z.land prio_in 7))) (PreH10 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH11 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH12 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH13 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH14 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH15 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH16 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH17 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcb_prio_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  (store_osrdytbl sg rdyL_in )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (store_osrdytbl sg rdyL_in )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcb_prio_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_2 := OSMutex_RdyAtPrio_full_partial_solve_wit_2_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_2_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (0 <= tcb_y_out) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (tcb_y_out < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure_split_goal_4 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (pt <> tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_out)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (0 <= tcb_y_out) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (tcb_y_out < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure_split_goal_4 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (pt <> tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_out)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (0 <= tcb_y_out) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (tcb_y_out < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure_split_goal_4 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (pt = tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_out)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (0 <= tcb_y_out) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (tcb_y_out < 8) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure_split_goal_4 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= tcb_y_out) ” 
  &&  “ (tcb_y_out < 8) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ ((Z.land (Z.shiftr prio_in 3) 7) < 8) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (pt = tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_out)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (pt = tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  ((( &( "prio" ) )) # UChar  |-> prio_in)
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt = tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (pt = tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  ((( &( "prio" ) )) # UChar  |-> prio_in)
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (pt <> tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) = 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  ((( &( "prio" ) )) # UChar  |-> prio_in)
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (Z.land rdy_grp_in (unsigned_last_nbits ((Z.lnot tcb_bity_in)) (8))) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_aux.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ” 
  &&  “ (prio_in < 64) ”
).

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (0 <= prio_in) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> pt)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "y" ) )) # UChar  |-> tcb_y_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ”
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (tcb_bitx_out: Z) (tcb_bity_out: Z) (tcb_x_out: Z) (tcb_y_out: Z) (rdy_grp_out: Z) (rdy_tbl_new_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdy_tbl_y_in: Z) (prioL_out: (@list Z)) (rdyL_out: (@list Z)) (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (prio_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (X: (unit -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pt <> tcbcur_in)) (PreH2 : ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0)) (PreH3 : (prio_pre = prio_in)) (PreH4 : (pt = ptcb_pre)) (PreH5 : (pt <> 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X )) (PreH7 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) (PreH8 : (0 <= tcb_y_in)) (PreH9 : (tcb_y_in < 8)) (PreH10 : (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7))) (PreH11 : (tcb_x_out = (Z.land prio_in 7))) (PreH12 : (tcb_bity_out = (Z.shiftl 1 tcb_y_out))) (PreH13 : (tcb_bitx_out = (Z.shiftl 1 tcb_x_out))) (PreH14 : (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))))) (PreH15 : (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out)))) (PreH16 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) (PreH17 : (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out))) (PreH18 : (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)))))) (PreH19 : (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in)))) ,
  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
|--
  “ (prio_in < 64) ” 
  &&  “ (0 <= prio_in) ” 
  &&  “ (pt <> tcbcur_in) ” 
  &&  “ ((Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8))) <> 0) ” 
  &&  “ (prio_pre = prio_in) ” 
  &&  “ (pt = ptcb_pre) ” 
  &&  “ (pt <> 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((OSMutex_RdyAtPrio_atomic_cmd (sg) (ls0) (ptcb_pre) (prio_pre))) (observe_unit_void)) X ) ” 
  &&  “ ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in) ” 
  &&  “ (0 <= tcb_y_in) ” 
  &&  “ (tcb_y_in < 8) ” 
  &&  “ (tcb_y_out = (Z.land (Z.shiftr prio_in 3) 7)) ” 
  &&  “ (tcb_x_out = (Z.land prio_in 7)) ” 
  &&  “ (tcb_bity_out = (Z.shiftl 1 tcb_y_out)) ” 
  &&  “ (tcb_bitx_out = (Z.shiftl 1 tcb_x_out)) ” 
  &&  “ (rdy_tbl_y_out = (Z.land rdy_tbl_y_in (unsigned_last_nbits ((Z.lnot tcb_bitx_in)) (8)))) ” 
  &&  “ (rdy_grp_out = (ready_group_after_relocation (rdy_grp_in) (rdy_tbl_y_out) (tcb_bity_in) (tcb_bity_out))) ” 
  &&  “ (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0))) ” 
  &&  “ (rdy_tbl_new_y_out = (Z.lor rdy_tbl_new_y_in tcb_bitx_out)) ” 
  &&  “ (rdyL_out = (replace_Znth (tcb_y_out) (rdy_tbl_new_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))))) ” 
  &&  “ (prioL_out = (replace_Znth (prio_in) (pt) (prioL_in))) ”
  &&  ((( &( "prio" ) )) # UChar  |-> prio_in)
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (store_priotbl_list sg prioL_in )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_tbl_new_y_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8))))
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((pt)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (used_task_rdy_rest sg pt tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits (rdy_grp_in) (8)) (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (valid_priority_index (sg) (prio_in)) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (ready_owner_relocation_domain (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (tid) (old_t) (prio_in)) )
.

Definition OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner := OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure -> OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_aux.

Definition OSMutex_RdyAtPrio_full_which_implies_wit_1 := 
(
forall (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ptcb_v: Z) (PreH1 : (ptcb_v = pt)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcb_prio_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg ptcb_v tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  (store_osrdytbl sg rdyL_in )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
) \/
(
forall (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ptcb_v: Z) (PreH1 : (ptcb_v = pt)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcb_prio_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg ptcb_v tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  (store_osrdytbl sg rdyL_in )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
).

Definition OSMutex_RdyAtPrio_full_which_implies_wit_1_split_goal_spatial := 
forall (prioL_in: (@list Z)) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_bitx_in: Z) (tcb_bity_in: Z) (tcb_x_in: Z) (tcb_y_in: Z) (tcb_prio_in: Z) (tcbcur_in: Z) (pt: Z) (old_t: TaskAbstractState) (tid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ptcb_v: Z) (PreH1 : (ptcb_v = pt)) ,
  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> tcb_prio_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> tcb_x_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> tcb_bitx_in)
  **  ((&((ptcb_v)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> tcb_bity_in)
  **  (used_task_rdy_rest sg ptcb_v tid old_t )
  **  (task_inv_no_tid_priotbl sg (ls0.(TskState) ) tid )
  **  (store_priotbl_list sg prioL_in )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> rdy_grp_in)
  **  (store_osrdytbl sg rdyL_in )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_cur_in)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcbcur_in)
  **  (sched_inv_rest_ready_current sg (ls0.(TskState) ) (ls0.(SchedState) ) )
  **  (event_inv sg (ls0.(TskState) ) (ls0.(EventState) ) )
  **  (tick_inv sg (ls0.(TickState) ) )
  **  (coq_prop (cross_module_consistency (sg) (ls0)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (os_rdy_grp_addr (sg) (( &( "OSRdyGrp" ) ))) )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (os_prio_cur_addr (sg) (( &( "OSPrioCur" ) ))) )
  **  (coq_prop (os_tcb_cur_addr (sg) (( &( "OSTCBCur" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (task_rdy_snapshot_of_prop (sg) ((ls0.(TskState) )) (tid) (old_t) (pt) (tcb_prio_in) (tcb_x_in) (tcb_y_in) (tcb_bitx_in) (tcb_bity_in)) )
  **  (coq_prop (task_priority_fields_layout_prop (pt) (&((pt)  # "os_tcb" ->ₛ "OSTCBPrio")) (&((pt)  # "os_tcb" ->ₛ "OSTCBX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBY")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitX")) (&((pt)  # "os_tcb" ->ₛ "OSTCBBitY"))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (coq_prop (sched_tcb_cur_snapshot_prop (sg) ((ls0.(SchedState) )) (tcbcur_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutex_RdyAtPrio_full_which_implies_wit_2 := 
(
forall (rdy_tbl_y_in: Z) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_y_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= tcb_y_in)) (PreH2 : (tcb_y_in < 8)) (PreH3 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) ,
  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (store_osrdytbl sg rdyL_in )
|--
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_in)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
) \/
(
forall (rdy_tbl_y_in: Z) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_y_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= tcb_y_in)) (PreH2 : (tcb_y_in < 8)) (PreH3 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) ,
  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (store_osrdytbl sg rdyL_in )
|--
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_in)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
).

Definition OSMutex_RdyAtPrio_full_which_implies_wit_2_split_goal_spatial := 
forall (rdy_tbl_y_in: Z) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_y_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= tcb_y_in)) (PreH2 : (tcb_y_in < 8)) (PreH3 : ((Znth (tcb_y_in) (rdyL_in) (0)) = rdy_tbl_y_in)) ,
  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (store_osrdytbl sg rdyL_in )
|--
  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_in)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
.

Definition OSMutex_RdyAtPrio_full_which_implies_wit_3 := 
(
forall (tcb_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_y_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ptcb: Z) (PreH1 : (0 <= tcb_y_out)) (PreH2 : (tcb_y_out < 8)) (PreH3 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) ,
  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_out)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> tcb_y_out)
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_new_y_in)
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
) \/
(
forall (tcb_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_y_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= tcb_y_out)) (PreH2 : (tcb_y_out < 8)) (PreH3 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) ,
  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_out)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
|--
  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_new_y_in)
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
).

Definition OSMutex_RdyAtPrio_full_which_implies_wit_3_split_goal_spatial := 
forall (tcb_y_out: Z) (rdy_tbl_new_y_in: Z) (rdy_tbl_y_out: Z) (rdyL_in: (@list Z)) (prio_cur_in: Z) (rdy_grp_in: Z) (tcb_y_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= tcb_y_out)) (PreH2 : (tcb_y_out < 8)) (PreH3 : (rdy_tbl_new_y_in = (Znth (tcb_y_out) ((replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in))) (0)))) ,
  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
  **  (((( &( "OSRdyTbl" ) ) + (tcb_y_in * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_y_out)
  **  (store_osrdytbl_missing_i sg rdyL_in tcb_y_in )
|--
  (((( &( "OSRdyTbl" ) ) + (tcb_y_out * sizeof(UCHAR)))) # UChar  |-> rdy_tbl_new_y_in)
  **  (store_osrdytbl_missing_i sg (replace_Znth (tcb_y_in) (rdy_tbl_y_out) (rdyL_in)) tcb_y_out )
  **  (coq_prop (os_rdy_tbl_addr (sg) (( &( "OSRdyTbl" ) ))) )
  **  (coq_prop (sched_ready_prio_snapshot_prop (sg) ((ls0.(TskState) )) ((ls0.(SchedState) )) (rdy_grp_in) (rdyL_in) (prio_cur_in)) )
.

Definition OSMutex_RdyAtPrio_full_which_implies_wit_4 := 
(
forall (prioL_in: (@list Z)) (prio_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (store_priotbl_list sg prioL_in )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
) \/
(
forall (prioL_in: (@list Z)) (prio_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (store_priotbl_list sg prioL_in )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
).

Definition OSMutex_RdyAtPrio_full_which_implies_wit_4_split_goal_spatial := 
forall (prioL_in: (@list Z)) (prio_in: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (0 <= prio_in)) (PreH2 : (prio_in < 64)) ,
  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (store_priotbl_list sg prioL_in )
|--
  (((( &( "OSTCBPrioTbl" ) ) + (prio_in * sizeof(PTR)))) # Ptr  |-> (Znth (prio_in) (prioL_in) (0)))
  **  (store_priotbl_list_missing_i sg prioL_in prio_in )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Module Type VC_Correct.


Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_1_current_owner : OSMutex_RdyAtPrio_full_safety_wit_1_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_2_current_owner : OSMutex_RdyAtPrio_full_safety_wit_2_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_3_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_4_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_5_current_owner : OSMutex_RdyAtPrio_full_safety_wit_5_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_6_current_owner : OSMutex_RdyAtPrio_full_safety_wit_6_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_7_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_7_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_8_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_8_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_9_current_owner : OSMutex_RdyAtPrio_full_safety_wit_9_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_10_current_owner : OSMutex_RdyAtPrio_full_safety_wit_10_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_11_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_11_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_safety_wit_12_noncurrent_owner : OSMutex_RdyAtPrio_full_safety_wit_12_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_return_wit_1_noncurrent_owner : OSMutex_RdyAtPrio_full_return_wit_1_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_return_wit_2_noncurrent_owner : OSMutex_RdyAtPrio_full_return_wit_2_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_return_wit_3_current_owner : OSMutex_RdyAtPrio_full_return_wit_3_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_return_wit_4_current_owner : OSMutex_RdyAtPrio_full_return_wit_4_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_1_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_1_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_1 : OSMutex_RdyAtPrio_full_partial_solve_wit_1.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_2_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_2_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_2 : OSMutex_RdyAtPrio_full_partial_solve_wit_2.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_3_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_4_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_5_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_6_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_7_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_8_current_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_9_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure : OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner_pure.
Axiom proof_of_OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner : OSMutex_RdyAtPrio_full_partial_solve_wit_10_noncurrent_owner.
Axiom proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_1 : OSMutex_RdyAtPrio_full_which_implies_wit_1.
Axiom proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_2 : OSMutex_RdyAtPrio_full_which_implies_wit_2.
Axiom proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_3 : OSMutex_RdyAtPrio_full_which_implies_wit_3.
Axiom proof_of_OSMutex_RdyAtPrio_full_which_implies_wit_4 : OSMutex_RdyAtPrio_full_which_implies_wit_4.

End VC_Correct.
