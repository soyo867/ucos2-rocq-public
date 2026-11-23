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
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_del_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Local Open Scope sac.

(*----- Function OSMutexDel_FirstSet8 -----*)

Definition OSMutexDel_FirstSet8_return_wit_1 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 64) = 0)) (PreH2 : ((Z.land bits_pre 32) = 0)) (PreH3 : ((Z.land bits_pre 16) = 0)) (PreH4 : ((Z.land bits_pre 8) = 0)) (PreH5 : ((Z.land bits_pre 4) = 0)) (PreH6 : ((Z.land bits_pre 2) = 0)) (PreH7 : ((Z.land bits_pre 1) = 0)) (PreH8 : (bits_pre = bits_in)) (PreH9 : (0 <= bits_in)) (PreH10 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (7 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 7) ” 
  &&  “ (7 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 64) = 0)) (PreH2 : ((Z.land bits_pre 32) = 0)) (PreH3 : ((Z.land bits_pre 16) = 0)) (PreH4 : ((Z.land bits_pre 8) = 0)) (PreH5 : ((Z.land bits_pre 4) = 0)) (PreH6 : ((Z.land bits_pre 2) = 0)) (PreH7 : ((Z.land bits_pre 1) = 0)) (PreH8 : (bits_pre = bits_in)) (PreH9 : (0 <= bits_in)) (PreH10 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (7 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_1_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 64) = 0)) (PreH2 : ((Z.land bits_pre 32) = 0)) (PreH3 : ((Z.land bits_pre 16) = 0)) (PreH4 : ((Z.land bits_pre 8) = 0)) (PreH5 : ((Z.land bits_pre 4) = 0)) (PreH6 : ((Z.land bits_pre 2) = 0)) (PreH7 : ((Z.land bits_pre 1) = 0)) (PreH8 : (bits_pre = bits_in)) (PreH9 : (0 <= bits_in)) (PreH10 : (bits_in <= 255)) ,
  (7 = (mutex_del_first_set8 (bits_pre)))
.

Definition OSMutexDel_FirstSet8_return_wit_2 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 64) <> 0)) (PreH2 : ((Z.land bits_pre 32) = 0)) (PreH3 : ((Z.land bits_pre 16) = 0)) (PreH4 : ((Z.land bits_pre 8) = 0)) (PreH5 : ((Z.land bits_pre 4) = 0)) (PreH6 : ((Z.land bits_pre 2) = 0)) (PreH7 : ((Z.land bits_pre 1) = 0)) (PreH8 : (bits_pre = bits_in)) (PreH9 : (0 <= bits_in)) (PreH10 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (6 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 6) ” 
  &&  “ (6 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 64) <> 0)) (PreH2 : ((Z.land bits_pre 32) = 0)) (PreH3 : ((Z.land bits_pre 16) = 0)) (PreH4 : ((Z.land bits_pre 8) = 0)) (PreH5 : ((Z.land bits_pre 4) = 0)) (PreH6 : ((Z.land bits_pre 2) = 0)) (PreH7 : ((Z.land bits_pre 1) = 0)) (PreH8 : (bits_pre = bits_in)) (PreH9 : (0 <= bits_in)) (PreH10 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (6 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_2_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 64) <> 0)) (PreH2 : ((Z.land bits_pre 32) = 0)) (PreH3 : ((Z.land bits_pre 16) = 0)) (PreH4 : ((Z.land bits_pre 8) = 0)) (PreH5 : ((Z.land bits_pre 4) = 0)) (PreH6 : ((Z.land bits_pre 2) = 0)) (PreH7 : ((Z.land bits_pre 1) = 0)) (PreH8 : (bits_pre = bits_in)) (PreH9 : (0 <= bits_in)) (PreH10 : (bits_in <= 255)) ,
  (6 = (mutex_del_first_set8 (bits_pre)))
.

Definition OSMutexDel_FirstSet8_return_wit_3 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 32) <> 0)) (PreH2 : ((Z.land bits_pre 16) = 0)) (PreH3 : ((Z.land bits_pre 8) = 0)) (PreH4 : ((Z.land bits_pre 4) = 0)) (PreH5 : ((Z.land bits_pre 2) = 0)) (PreH6 : ((Z.land bits_pre 1) = 0)) (PreH7 : (bits_pre = bits_in)) (PreH8 : (0 <= bits_in)) (PreH9 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (5 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 5) ” 
  &&  “ (5 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 32) <> 0)) (PreH2 : ((Z.land bits_pre 16) = 0)) (PreH3 : ((Z.land bits_pre 8) = 0)) (PreH4 : ((Z.land bits_pre 4) = 0)) (PreH5 : ((Z.land bits_pre 2) = 0)) (PreH6 : ((Z.land bits_pre 1) = 0)) (PreH7 : (bits_pre = bits_in)) (PreH8 : (0 <= bits_in)) (PreH9 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (5 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_3_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 32) <> 0)) (PreH2 : ((Z.land bits_pre 16) = 0)) (PreH3 : ((Z.land bits_pre 8) = 0)) (PreH4 : ((Z.land bits_pre 4) = 0)) (PreH5 : ((Z.land bits_pre 2) = 0)) (PreH6 : ((Z.land bits_pre 1) = 0)) (PreH7 : (bits_pre = bits_in)) (PreH8 : (0 <= bits_in)) (PreH9 : (bits_in <= 255)) ,
  (5 = (mutex_del_first_set8 (bits_pre)))
.

Definition OSMutexDel_FirstSet8_return_wit_4 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 16) <> 0)) (PreH2 : ((Z.land bits_pre 8) = 0)) (PreH3 : ((Z.land bits_pre 4) = 0)) (PreH4 : ((Z.land bits_pre 2) = 0)) (PreH5 : ((Z.land bits_pre 1) = 0)) (PreH6 : (bits_pre = bits_in)) (PreH7 : (0 <= bits_in)) (PreH8 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (4 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 4) ” 
  &&  “ (4 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 16) <> 0)) (PreH2 : ((Z.land bits_pre 8) = 0)) (PreH3 : ((Z.land bits_pre 4) = 0)) (PreH4 : ((Z.land bits_pre 2) = 0)) (PreH5 : ((Z.land bits_pre 1) = 0)) (PreH6 : (bits_pre = bits_in)) (PreH7 : (0 <= bits_in)) (PreH8 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (4 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_4_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 16) <> 0)) (PreH2 : ((Z.land bits_pre 8) = 0)) (PreH3 : ((Z.land bits_pre 4) = 0)) (PreH4 : ((Z.land bits_pre 2) = 0)) (PreH5 : ((Z.land bits_pre 1) = 0)) (PreH6 : (bits_pre = bits_in)) (PreH7 : (0 <= bits_in)) (PreH8 : (bits_in <= 255)) ,
  (4 = (mutex_del_first_set8 (bits_pre)))
.

Definition OSMutexDel_FirstSet8_return_wit_5 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 8) <> 0)) (PreH2 : ((Z.land bits_pre 4) = 0)) (PreH3 : ((Z.land bits_pre 2) = 0)) (PreH4 : ((Z.land bits_pre 1) = 0)) (PreH5 : (bits_pre = bits_in)) (PreH6 : (0 <= bits_in)) (PreH7 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (3 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 3) ” 
  &&  “ (3 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 8) <> 0)) (PreH2 : ((Z.land bits_pre 4) = 0)) (PreH3 : ((Z.land bits_pre 2) = 0)) (PreH4 : ((Z.land bits_pre 1) = 0)) (PreH5 : (bits_pre = bits_in)) (PreH6 : (0 <= bits_in)) (PreH7 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (3 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_5_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 8) <> 0)) (PreH2 : ((Z.land bits_pre 4) = 0)) (PreH3 : ((Z.land bits_pre 2) = 0)) (PreH4 : ((Z.land bits_pre 1) = 0)) (PreH5 : (bits_pre = bits_in)) (PreH6 : (0 <= bits_in)) (PreH7 : (bits_in <= 255)) ,
  (3 = (mutex_del_first_set8 (bits_pre)))
.

Definition OSMutexDel_FirstSet8_return_wit_6 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 4) <> 0)) (PreH2 : ((Z.land bits_pre 2) = 0)) (PreH3 : ((Z.land bits_pre 1) = 0)) (PreH4 : (bits_pre = bits_in)) (PreH5 : (0 <= bits_in)) (PreH6 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (2 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 2) ” 
  &&  “ (2 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 4) <> 0)) (PreH2 : ((Z.land bits_pre 2) = 0)) (PreH3 : ((Z.land bits_pre 1) = 0)) (PreH4 : (bits_pre = bits_in)) (PreH5 : (0 <= bits_in)) (PreH6 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (2 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_6_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 4) <> 0)) (PreH2 : ((Z.land bits_pre 2) = 0)) (PreH3 : ((Z.land bits_pre 1) = 0)) (PreH4 : (bits_pre = bits_in)) (PreH5 : (0 <= bits_in)) (PreH6 : (bits_in <= 255)) ,
  (2 = (mutex_del_first_set8 (bits_pre)))
.

Definition OSMutexDel_FirstSet8_return_wit_7 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 2) <> 0)) (PreH2 : ((Z.land bits_pre 1) = 0)) (PreH3 : (bits_pre = bits_in)) (PreH4 : (0 <= bits_in)) (PreH5 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (1 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 2) <> 0)) (PreH2 : ((Z.land bits_pre 1) = 0)) (PreH3 : (bits_pre = bits_in)) (PreH4 : (0 <= bits_in)) (PreH5 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (1 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_7_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 2) <> 0)) (PreH2 : ((Z.land bits_pre 1) = 0)) (PreH3 : (bits_pre = bits_in)) (PreH4 : (0 <= bits_in)) (PreH5 : (bits_in <= 255)) ,
  (1 = (mutex_del_first_set8 (bits_pre)))
.

Definition OSMutexDel_FirstSet8_return_wit_8 := 
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 1) <> 0)) (PreH2 : (bits_pre = bits_in)) (PreH3 : (0 <= bits_in)) (PreH4 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (0 = (mutex_del_first_set8 (bits_in))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 8) ”
  &&  emp
) \/
(
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 1) <> 0)) (PreH2 : (bits_pre = bits_in)) (PreH3 : (0 <= bits_in)) (PreH4 : (bits_in <= 255)) ,
  TT && emp 
|--
  “ (0 = (mutex_del_first_set8 (bits_pre))) ”
  &&  emp
).

Definition OSMutexDel_FirstSet8_return_wit_8_split_goal_1 := 
forall (bits_pre: Z) (bits_in: Z) (PreH1 : ((Z.land bits_pre 1) <> 0)) (PreH2 : (bits_pre = bits_in)) (PreH3 : (0 <= bits_in)) (PreH4 : (bits_in <= 255)) ,
  (0 = (mutex_del_first_set8 (bits_pre)))
.

(*----- Function OSMutexDel_RefreshHighReady -----*)

Definition OSMutexDel_RefreshHighReady_safety_wit_1 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 255)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_RefreshHighReady_return_wit_1 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (mutex_del_restore_rep false sg entry post )
  **  (InsideCritical sg critical_anchor )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_restore_rep false sg entry post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_return_wit_2 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (mutex_del_restore_rep false sg entry post )
  **  (InsideCritical sg critical_anchor )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_restore_rep false sg entry post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_1 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg entry post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg entry post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_2_pure := 
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) = 0) ”
) \/
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) = 0) ”
).

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_2_pure_split_goal_1 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) = 0) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_2_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((mutex_del_refresh_grp_value (post)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0) ”
  &&  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_2 := OSMutexDel_RefreshHighReady_partial_solve_wit_2_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_2_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_3 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 255)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0) ”
  &&  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 255)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_4 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0)) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) = 0) ”
  &&  (mutex_del_refresh_closed_inv sg post )
  **  (InsideCritical sg critical_anchor )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure := 
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) = (mutex_del_refresh_grp_value (post))) ” 
  &&  “ ((mutex_del_refresh_grp_value (post)) <= 255) ” 
  &&  “ (0 <= (mutex_del_refresh_grp_value (post))) ”
) \/
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ (0 <= (mutex_del_refresh_grp_value (post))) ” 
  &&  “ ((mutex_del_refresh_grp_value (post)) <= 255) ”
).

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure_split_goal_1 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ (0 <= (mutex_del_refresh_grp_value (post))) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure_split_goal_2 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) <= 255) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_5_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (PreH1 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ ((mutex_del_refresh_grp_value (post)) = (mutex_del_refresh_grp_value (post))) ” 
  &&  “ ((mutex_del_refresh_grp_value (post)) <= 255) ” 
  &&  “ (0 <= (mutex_del_refresh_grp_value (post))) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_5 := OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_5_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_6_pure := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |-> retval)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) < 8) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_6_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "y" ) )) # UChar  |-> retval)
|--
  “ ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) < 8) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_6 := OSMutexDel_RefreshHighReady_partial_solve_wit_6_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_6_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_7_pure := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  (((( &( "OSRdyTbl" ) ) + ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)) = (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_7_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (((( &( "OSRdyTbl" ) ) + ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
|--
  “ ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)) = (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_7 := OSMutexDel_RefreshHighReady_partial_solve_wit_7_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_7_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure := 
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)) = (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ” 
  &&  “ (0 <= (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ” 
  &&  “ ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ” 
  &&  “ ((Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ” 
  &&  “ (0 <= (Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ”
) \/
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ (0 <= (Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ” 
  &&  “ ((Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ” 
  &&  “ ((Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ” 
  &&  “ (0 <= (Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ”
).

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure_split_goal_1 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ (0 <= (Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure_split_goal_2 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure_split_goal_3 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure_split_goal_4 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |->_)
  **  ((( &( "x" ) )) # UChar  |->_)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ (0 <= (Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_8_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (PreH1 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 8)) (PreH4 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
|--
  “ ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)) = (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ” 
  &&  “ (0 <= (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ” 
  &&  “ ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ” 
  &&  “ ((Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0)) <= 255) ” 
  &&  “ (0 <= (Znth (retval) ((mutex_del_refresh_ready_tbl_values (post))) (0))) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_8 := OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_8_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_9_pure := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |->_)
  **  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + retval_2 ))
  **  ((( &( "x" ) )) # UChar  |-> retval_2)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ” 
  &&  “ (0 <= (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ” 
  &&  “ ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) < 64) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_9_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + retval_2 ))
|--
  “ ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ” 
  &&  “ (0 <= (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ” 
  &&  “ ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) < 64) ” 
  &&  “ (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 8) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_9 := OSMutexDel_RefreshHighReady_partial_solve_wit_9_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_9_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_10_pure := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "high_tcb" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  ((( &( "x" ) )) # UChar  |-> retval_2)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ” 
  &&  “ ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)) = (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0))) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_10_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
|--
  “ ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ” 
  &&  “ ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)) = (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0))) ” 
  &&  “ (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 8) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_10 := OSMutexDel_RefreshHighReady_partial_solve_wit_10_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_10_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_11_pure := 
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "high_tcb" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "x" ) )) # UChar  |-> retval_2)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) <> 0) ”
) \/
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "high_tcb" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "x" ) )) # UChar  |-> retval_2)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) <> 0) ”
).

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_11_pure_split_goal_1 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "high_tcb" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  ((( &( "x" ) )) # UChar  |-> retval_2)
  **  ((( &( "grp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
|--
  “ ((mutex_del_refresh_grp_value (post)) <> 0) ”
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_11_aux := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (old_high_tcb: Z) (old_high_prio: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
|--
  “ ((mutex_del_refresh_grp_value (post)) <> 0) ” 
  &&  “ (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 8) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_11 := OSMutexDel_RefreshHighReady_partial_solve_wit_11_pure -> OSMutexDel_RefreshHighReady_partial_solve_wit_11_aux.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_12 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
|--
  “ (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 8) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_partial_solve_wit_13 := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 8)) (PreH4 : (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 8)) (PreH7 : ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0)) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (retval_2 = (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0))))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 8) ” 
  &&  “ (retval = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 8) ” 
  &&  “ ((unsigned_last_nbits ((mutex_del_refresh_grp_value (post))) (32)) <> 0) ”
  &&  (mutex_del_refresh_closed_inv sg post )
  **  (InsideCritical sg critical_anchor )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_1 := 
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg entry post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (old_high_tcb: Z)  (old_high_prio: Z) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg entry post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (old_high_tcb: Z)  (old_high_prio: Z) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> old_high_prio)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> old_high_tcb)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_2 := 
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((mutex_del_refresh_grp_value (post)) = 0)) ,
  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
|--
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
) \/
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((mutex_del_refresh_grp_value (post)) = 0)) ,
  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
|--
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_2_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((mutex_del_refresh_grp_value (post)) = 0)) ,
  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
|--
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_3 := 
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 255)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 255)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_3_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 255)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) (255) (0)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_4 := 
(
forall (post: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_refresh_closed_inv sg post )
|--
  (mutex_del_restore_rep false sg entry post )
) \/
(
forall (post: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_refresh_closed_inv sg post )
|--
  (mutex_del_restore_rep false sg entry post )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_4_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_refresh_closed_inv sg post )
|--
  (mutex_del_restore_rep false sg entry post )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_5 := 
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (y: Z) (PreH1 : (y = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= y)) (PreH3 : (y < 8)) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  (((( &( "OSRdyTbl" ) ) + ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (y: Z) (PreH1 : (y = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= y)) (PreH3 : (y < 8)) ,
  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (((( &( "OSRdyTbl" ) ) + ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_5_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (y: Z) (PreH1 : (y = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (0 <= y)) (PreH3 : (y < 8)) ,
  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (((( &( "OSRdyTbl" ) ) + ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * sizeof(UCHAR)))) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_6 := 
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (y: Z) (row: Z) (PreH1 : (y = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (row = (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "row" ) )) # UChar  |-> row)
  **  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> row)
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) y )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  ((( &( "y" ) )) # UChar  |-> (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))
  **  ((( &( "row" ) )) # UChar  |-> (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (y: Z) (row: Z) (PreH1 : (y = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (row = (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ,
  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> row)
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) y )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_6_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (y: Z) (row: Z) (PreH1 : (y = (mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))))) (PreH2 : (row = (Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ,
  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> row)
  **  (store_osrdytbl_missing_i sg (mutex_del_refresh_ready_tbl_values (post)) y )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_7 := 
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (high_prio: Z) (PreH1 : (high_prio = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))) (PreH2 : (0 <= high_prio)) (PreH3 : (high_prio < 64)) ,
  ((( &( "high_prio" ) )) # UChar  |-> high_prio)
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (high_prio: Z) (PreH1 : (high_prio = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))) (PreH2 : (0 <= high_prio)) (PreH3 : (high_prio < 64)) ,
  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (((( &( "OSTCBPrioTbl" ) ) + ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_7_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (high_prio: Z) (PreH1 : (high_prio = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))) (PreH2 : (0 <= high_prio)) (PreH3 : (high_prio < 64)) ,
  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (((( &( "OSTCBPrioTbl" ) ) + ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) * sizeof(PTR)))) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_8 := 
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (high_prio: Z) (high_tcb: Z) (PreH1 : (high_prio = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))) (PreH2 : (high_tcb = (Znth (high_prio) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) ,
  ((( &( "high_prio" ) )) # UChar  |-> high_prio)
  **  ((( &( "high_tcb" ) )) # Ptr  |-> high_tcb)
  **  (((( &( "OSTCBPrioTbl" ) ) + (high_prio * sizeof(PTR)))) # Ptr  |-> high_tcb)
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) high_prio )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  ((( &( "high_prio" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "high_tcb" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (high_prio: Z) (high_tcb: Z) (PreH1 : (high_prio = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))) (PreH2 : (high_tcb = (Znth (high_prio) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (high_prio * sizeof(PTR)))) # Ptr  |-> high_tcb)
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) high_prio )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_8_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (high_prio: Z) (high_tcb: Z) (PreH1 : (high_prio = (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))) (PreH2 : (high_tcb = (Znth (high_prio) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) ,
  (((( &( "OSTCBPrioTbl" ) ) + (high_prio * sizeof(PTR)))) # Ptr  |-> high_tcb)
  **  (store_priotbl_list_missing_i sg (mutex_del_refresh_prio_tbl_values (sg) (post)) high_prio )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_9 := 
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((mutex_del_refresh_grp_value (post)) <> 0)) ,
  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
|--
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
) \/
(
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((mutex_del_refresh_grp_value (post)) <> 0)) ,
  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
|--
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_9_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((mutex_del_refresh_grp_value (post)) <> 0)) ,
  (coq_prop (mutex_del_refresh_snapshot_prop (sg) (post) ((mutex_del_refresh_grp_value (post))) ((mutex_del_refresh_ready_tbl_values (post))) ((mutex_del_refresh_prio_tbl_values (sg) (post)))) )
|--
  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_10 := 
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_10_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (InsideCritical sg critical_anchor )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_del_refresh_grp_value (post)))
  **  (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values (post)) )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) ))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))
  **  (store_priotbl_list sg (mutex_del_refresh_prio_tbl_values (sg) (post)) )
  **  (mutex_del_refresh_residual sg post )
  **  (coq_prop (mutex_del_refresh_choice_prop (sg) (post) ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((Znth ((((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post)))) * 8 ) + (mutex_del_first_set8 ((Znth ((mutex_del_first_set8 ((mutex_del_refresh_grp_value (post))))) ((mutex_del_refresh_ready_tbl_values (post))) (0)))) )) ((mutex_del_refresh_prio_tbl_values (sg) (post))) (0)))) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (post)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_refresh_closed_inv sg post )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_RefreshHighReady_which_implies_wit_11 := 
(
forall (post: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_refresh_closed_inv sg post )
|--
  (mutex_del_restore_rep false sg entry post )
) \/
(
forall (post: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_refresh_closed_inv sg post )
|--
  (mutex_del_restore_rep false sg entry post )
).

Definition OSMutexDel_RefreshHighReady_which_implies_wit_11_split_goal_spatial := 
forall (post: UCOS2_Verify_State) (entry: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_refresh_closed_inv sg post )
|--
  (mutex_del_restore_rep false sg entry post )
.

(*----- Function OSMutexDel_full -----*)

Definition OSMutexDel_full_safety_wit_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (perr_pre <> 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (pe = pevent_pre)) (PreH4 : (pd = perr_pre)) (PreH5 : (opt_pre = opt_in)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH7 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_safety_wit_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (pe = pe)) (PreH3 : (pe = pevent_pre)) (PreH4 : (pe <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= etype)) (PreH7 : (etype <= 255)) (PreH8 : (etype <> 4)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ False ”
.

Definition OSMutexDel_full_safety_wit_3 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexDel_full_safety_wit_3_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= ecnt_in) ”
.

Definition OSMutexDel_full_safety_wit_3_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (8 <= 31) ”
.

Definition OSMutexDel_full_safety_wit_3_split_goal_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= 8) ”
.

Definition OSMutexDel_full_safety_wit_4 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_safety_wit_5 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (ptcb_v: Z) (perr: Z) (pevent: Z) (old_pcp_cell: Z) (owner_post: UCOS2_Verify_State) (PreH1 : (pcp_v <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg owner_post )
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_v * sizeof(PTR)))) # Ptr  |-> old_pcp_cell)
  **  (mutex_del_event_missing_priotbl_focus sg ls0 owner_post eid pcp_v )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_safety_wit_6 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (cpu_sr_v: Z) (perr: Z) (pevent: Z) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_no_pend_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> 0)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_safety_wit_7 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexDel_full_safety_wit_7_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= ecnt_in) ”
.

Definition OSMutexDel_full_safety_wit_7_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (8 <= 31) ”
.

Definition OSMutexDel_full_safety_wit_7_split_goal_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= 8) ”
.

Definition OSMutexDel_full_safety_wit_8 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 <> opt_in)) (PreH10 : (1 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_safety_wit_9 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp_v: Z) (cpu_sr_v: Z) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits (egrp_loop) (32)) <> 0)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_safety_wit_10 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= ecnt_in) ” 
  &&  “ (8 <= 31) ” 
  &&  “ (0 <= 8) ”
).

Definition OSMutexDel_full_safety_wit_10_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= ecnt_in) ”
.

Definition OSMutexDel_full_safety_wit_10_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (8 <= 31) ”
.

Definition OSMutexDel_full_safety_wit_10_split_goal_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= 8) ”
.

Definition OSMutexDel_full_safety_wit_11 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (old_pcp_cell: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) * sizeof(PTR)))) # Ptr  |-> old_pcp_cell)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (mutex_del_abort_loop_missing_priotbl_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_safety_wit_12 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (cpu_sr_v: Z) (perr: Z) (pevent: Z) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> 0)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMutexDel_full_entail_wit_1 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (etype = 4)) (PreH8 : (pe = pevent_pre)) (PreH9 : (pe <> 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (0 <= etype)) (PreH12 : (etype <= 255)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (pe = pevent_pre)) (PreH17 : (pd = perr_pre)) (PreH18 : (opt_pre = opt_in)) (PreH19 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH20 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH21 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> pd)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((pd) # UChar  |-> perr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (etype = 4)) (PreH8 : (pe = pevent_pre)) (PreH9 : (pe <> 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (0 <= etype)) (PreH12 : (etype <= 255)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (pe = pevent_pre)) (PreH17 : (pd = perr_pre)) (PreH18 : (opt_pre = opt_in)) (PreH19 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH20 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH21 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
).

Definition OSMutexDel_full_entail_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (etype = 4)) (PreH8 : (pe = pevent_pre)) (PreH9 : (pe <> 0)) (PreH10 : (pe = (event_addr (sg) (eid)))) (PreH11 : (0 <= etype)) (PreH12 : (etype <= 255)) (PreH13 : (pevent_pre <> 0)) (PreH14 : (perr_pre <> 0)) (PreH15 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH16 : (pe = pevent_pre)) (PreH17 : (pd = perr_pre)) (PreH18 : (opt_pre = opt_in)) (PreH19 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH20 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH21 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
.

Definition OSMutexDel_full_entail_wit_2_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((pd) # UChar  |-> perr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pe) (1)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((pd) # UChar  |-> perr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pe) (1)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
).

Definition OSMutexDel_full_entail_wit_2_1_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (owner_orig = (Z.land ecnt_in 255)) ”
.

Definition OSMutexDel_full_entail_wit_2_1_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ”
.

Definition OSMutexDel_full_entail_wit_2_1_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) <> 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pe) (1)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_entail_wit_2_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((pd) # UChar  |-> perr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pe) (0)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((pd) # UChar  |-> perr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pe) (0)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
).

Definition OSMutexDel_full_entail_wit_2_2_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (owner_orig = (Z.land ecnt_in 255)) ”
.

Definition OSMutexDel_full_entail_wit_2_2_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ”
.

Definition OSMutexDel_full_entail_wit_2_2_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (egrp_in) (32)) = 0)) (PreH2 : (RTrans_C sg ls0 sg ls0 )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (etype = 4)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_enter_critical_call_prop (sg) (ls0) (ls0)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pe) (0)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_entail_wit_3_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (eptr_in <> 0)) (PreH2 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (eptr_in <> 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH6 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH8 : (eptr_in <> 0)) (PreH9 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH10 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (isr <= 0)) (PreH14 : (pevent = (event_addr (sg) (eid)))) (PreH15 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH16 : (owner_orig = (Z.land ecnt_in 255))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH18 : (0 = opt_in)) ,
  (InsideCritical sg ls_rdy )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_owner_ready_call_prop (sg) (owner_tid) (eptr_in) ((Z.land ecnt_in 255)) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_selected_event_noninterference_prop (eid) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (eptr_in <> 0)) (PreH2 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (eptr_in <> 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH6 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH8 : (eptr_in <> 0)) (PreH9 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH10 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (isr <= 0)) (PreH14 : (pevent = (event_addr (sg) (eid)))) (PreH15 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH16 : (owner_orig = (Z.land ecnt_in 255))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH18 : (0 = opt_in)) ,
  (InsideCritical sg ls_rdy )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_owner_ready_call_prop (sg) (owner_tid) (eptr_in) ((Z.land ecnt_in 255)) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_selected_event_noninterference_prop (eid) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
).

Definition OSMutexDel_full_entail_wit_3_1_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (eptr_in <> 0)) (PreH2 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (eptr_in <> 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH6 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH8 : (eptr_in <> 0)) (PreH9 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH10 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (isr <= 0)) (PreH14 : (pevent = (event_addr (sg) (eid)))) (PreH15 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH16 : (owner_orig = (Z.land ecnt_in 255))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH18 : (0 = opt_in)) ,
  (InsideCritical sg ls_rdy )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_owner_ready_call_prop (sg) (owner_tid) (eptr_in) ((Z.land ecnt_in 255)) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_selected_event_noninterference_prop (eid) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
.

Definition OSMutexDel_full_entail_wit_3_1_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (eptr_in <> 0)) (PreH2 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (eptr_in <> 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH6 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH8 : (eptr_in <> 0)) (PreH9 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH10 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH11 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (isr <= 0)) (PreH14 : (pevent = (event_addr (sg) (eid)))) (PreH15 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH16 : (owner_orig = (Z.land ecnt_in 255))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH18 : (0 = opt_in)) ,
  (InsideCritical sg ls_rdy )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_owner_ready_call_prop (sg) (owner_tid) (eptr_in) ((Z.land ecnt_in 255)) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_selected_event_noninterference_prop (eid) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
.

Definition OSMutexDel_full_entail_wit_3_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio <> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pevent = (event_addr (sg) (eid)))) (PreH10 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH11 : (owner_orig = (Z.land ecnt_in 255))) (PreH12 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH13 : (0 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio <> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pevent = (event_addr (sg) (eid)))) (PreH10 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH11 : (owner_orig = (Z.land ecnt_in 255))) (PreH12 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH13 : (0 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
).

Definition OSMutexDel_full_entail_wit_3_2_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio <> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pevent = (event_addr (sg) (eid)))) (PreH10 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH11 : (owner_orig = (Z.land ecnt_in 255))) (PreH12 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH13 : (0 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
.

Definition OSMutexDel_full_entail_wit_3_2_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio <> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pevent = (event_addr (sg) (eid)))) (PreH10 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH11 : (owner_orig = (Z.land ecnt_in 255))) (PreH12 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH13 : (0 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
.

Definition OSMutexDel_full_entail_wit_3_3 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (pevent = (event_addr (sg) (eid)))) (PreH8 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH9 : (owner_orig = (Z.land ecnt_in 255))) (PreH10 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH11 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (pevent = (event_addr (sg) (eid)))) (PreH8 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH9 : (owner_orig = (Z.land ecnt_in 255))) (PreH10 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH11 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
).

Definition OSMutexDel_full_entail_wit_3_3_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (pevent = (event_addr (sg) (eid)))) (PreH8 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH9 : (owner_orig = (Z.land ecnt_in 255))) (PreH10 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH11 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
.

Definition OSMutexDel_full_entail_wit_3_3_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (pevent = (event_addr (sg) (eid)))) (PreH8 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH9 : (owner_orig = (Z.land ecnt_in 255))) (PreH10 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH11 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
.

Definition OSMutexDel_full_entail_wit_4_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (ptcb_v: Z) (perr: Z) (pevent: Z) (owner_post: UCOS2_Verify_State) (PreH1 : (pcp_v <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg owner_post )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_v * sizeof(PTR)))) # Ptr  |-> 0)
  **  (mutex_del_event_missing_priotbl_focus sg ls0 owner_post eid pcp_v )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_v)
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (perr: Z) (pevent: Z) (owner_post: UCOS2_Verify_State) (PreH1 : (pcp_v <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg owner_post )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_v * sizeof(PTR)))) # Ptr  |-> 0)
  **  (mutex_del_event_missing_priotbl_focus sg ls0 owner_post eid pcp_v )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_full_entail_wit_4_1_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (perr: Z) (pevent: Z) (owner_post: UCOS2_Verify_State) (PreH1 : (pcp_v <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg owner_post )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp_v * sizeof(PTR)))) # Ptr  |-> 0)
  **  (mutex_del_event_missing_priotbl_focus sg ls0 owner_post eid pcp_v )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_full_entail_wit_4_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_full_entail_wit_4_2_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (egrp_in = 0) ”
.

Definition OSMutexDel_full_entail_wit_4_2_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_full_entail_wit_5 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v_2: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (tasks_v: Z) (current_tbl: (@list Z)) (current_event: OSEventAbstractState) (old_type: Z) (owner_post: UCOS2_Verify_State) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg owner_post )
  **  (mutex_del_pcp_release_focus sg ls0 owner_post eid pcp_v )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> freelist_in)
  **  (used_event_wait_table_storage (owner_post.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((owner_post.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((owner_post.(TskState) )) ((owner_post.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v_2)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((perr) # UChar  |-> perr_in)
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v_2: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (tasks_v: Z) (current_tbl: (@list Z)) (current_event: OSEventAbstractState) (old_type: Z) (owner_post: UCOS2_Verify_State) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg owner_post )
  **  (mutex_del_pcp_release_focus sg ls0 owner_post eid pcp_v )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> freelist_in)
  **  (used_event_wait_table_storage (owner_post.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((owner_post.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((owner_post.(TskState) )) ((owner_post.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v_2)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
).

Definition OSMutexDel_full_entail_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v_2: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (tasks_v: Z) (current_tbl: (@list Z)) (current_event: OSEventAbstractState) (old_type: Z) (owner_post: UCOS2_Verify_State) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg owner_post )
  **  (mutex_del_pcp_release_focus sg ls0 owner_post eid pcp_v )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> freelist_in)
  **  (used_event_wait_table_storage (owner_post.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((owner_post.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((owner_post.(TskState) )) ((owner_post.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v_2)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
.

Definition OSMutexDel_full_entail_wit_6 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls2)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  EX (perr_v: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_no_pend_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> perr_v)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls2)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_no_pend_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
).

Definition OSMutexDel_full_entail_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls2)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_no_pend_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
.

Definition OSMutexDel_full_entail_wit_7 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
).

Definition OSMutexDel_full_entail_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) <> 0)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
.

Definition OSMutexDel_full_entail_wit_8 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (ls0) (ls0) (ls2)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  EX (perr_v: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
  **  ((perr) # UChar  |-> perr_v)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (ls0) (ls0) (ls2)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
).

Definition OSMutexDel_full_entail_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (ls0) (ls0) (ls2)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
.

Definition OSMutexDel_full_entail_wit_9_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (eptr_in <> 0)) (PreH2 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (eptr_in <> 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH6 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH8 : (eptr_in <> 0)) (PreH9 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (isr <= 0)) (PreH13 : (pevent = (event_addr (sg) (eid)))) (PreH14 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH15 : (owner_orig = (Z.land ecnt_in 255))) (PreH16 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH17 : (0 <> opt_in)) (PreH18 : (1 = opt_in)) ,
  (InsideCritical sg ls_rdy )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_owner_ready_call_prop (sg) (owner_tid) (eptr_in) ((Z.land ecnt_in 255)) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_selected_event_noninterference_prop (eid) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_rdy: UCOS2_Verify_State) (PreH1 : (eptr_in <> 0)) (PreH2 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (eptr_in <> 0)) (PreH5 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH6 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH8 : (eptr_in <> 0)) (PreH9 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH10 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (isr <= 0)) (PreH13 : (pevent = (event_addr (sg) (eid)))) (PreH14 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH15 : (owner_orig = (Z.land ecnt_in 255))) (PreH16 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH17 : (0 <> opt_in)) (PreH18 : (1 = opt_in)) ,
  (InsideCritical sg ls_rdy )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_owner_ready_call_prop (sg) (owner_tid) (eptr_in) ((Z.land ecnt_in 255)) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_selected_event_noninterference_prop (eid) (ls0) (ls_rdy)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
).

Definition OSMutexDel_full_entail_wit_9_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio <> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pevent = (event_addr (sg) (eid)))) (PreH9 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH10 : (owner_orig = (Z.land ecnt_in 255))) (PreH11 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH12 : (0 <> opt_in)) (PreH13 : (1 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio <> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pevent = (event_addr (sg) (eid)))) (PreH9 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH10 : (owner_orig = (Z.land ecnt_in 255))) (PreH11 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH12 : (0 <> opt_in)) (PreH13 : (1 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
).

Definition OSMutexDel_full_entail_wit_9_3 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 <> opt_in)) (PreH11 : (1 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in = 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 <> opt_in)) (PreH11 : (1 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
).

Definition OSMutexDel_full_entail_wit_9_4 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 <> opt_in)) (PreH10 : (1 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (isr <= 0)) (PreH5 : (pevent = (event_addr (sg) (eid)))) (PreH6 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH7 : (owner_orig = (Z.land ecnt_in 255))) (PreH8 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH9 : (0 <> opt_in)) (PreH10 : (1 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
).

Definition OSMutexDel_full_entail_wit_10 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (ls_owner_cur_2: UCOS2_Verify_State) (ls_loop_2: UCOS2_Verify_State) (e_loop_2: OSEventAbstractState) (evtL_loop_2: (@list Z)) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop_2 )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop_2 eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur_2)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur_2) (ls_loop_2)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop_2.(TskState) )) ((ls_loop_2.(EventState) )) (eid) (e_loop_2) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_loop_2)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls_loop_2.(TskState) ) pevent e_loop_2 )
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  EX (e_loop: OSEventAbstractState)  (egrp_loop: Z)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
.

Definition OSMutexDel_full_entail_wit_11 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (egrp_loop_2: Z) (tasks_v: Z) (ls_owner_cur_2: UCOS2_Verify_State) (ls_loop_2: UCOS2_Verify_State) (pevent: Z) (perr: Z) (e_r: OSEventAbstractState) (egrp_out: Z) (evtL_out: (@list Z)) (ls_r: UCOS2_Verify_State) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits (egrp_loop_2) (32)) <> 0)) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg ls_r )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_r eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (ecnt_in) (eptr_in) (egrp_out) (evtL_out)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_out)
  **  (used_event_wait_table_storage (ls_r.(TskState) ) pevent e_r )
  **  (coq_prop (mutex_del_wake_step (sg) (eid) (ls_loop_2) (ls_r)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur_2)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur_2) (ls_loop_2)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  EX (e_loop: OSEventAbstractState)  (egrp_loop: Z)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (egrp_loop_2: Z) (tasks_v: Z) (ls_owner_cur_2: UCOS2_Verify_State) (ls_loop_2: UCOS2_Verify_State) (pevent: Z) (perr: Z) (e_r: OSEventAbstractState) (egrp_out: Z) (evtL_out: (@list Z)) (ls_r: UCOS2_Verify_State) (PreH1 : (pevent = (event_addr (sg) (eid)))) (PreH2 : ((unsigned_last_nbits (egrp_loop_2) (32)) <> 0)) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg ls_r )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_r eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_r.(TskState) )) ((ls_r.(EventState) )) (eid) (e_r) (4) (ecnt_in) (eptr_in) (egrp_out) (evtL_out)) )
  **  (used_event_wait_table_storage (ls_r.(TskState) ) pevent e_r )
  **  (coq_prop (mutex_del_wake_step (sg) (eid) (ls_loop_2) (ls_r)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur_2)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur_2) (ls_loop_2)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop_2.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (e_loop: OSEventAbstractState)  (evtL_loop: (@list Z))  (ls_owner_cur: UCOS2_Verify_State)  (ls_loop: UCOS2_Verify_State) ,
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_out) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
).

Definition OSMutexDel_full_entail_wit_12 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits (egrp_loop) (32)) = 0)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits (egrp_loop) (32)) = 0)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
|--
  “ (egrp_loop = 0) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_full_entail_wit_12_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits (egrp_loop) (32)) = 0)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
|--
  “ (egrp_loop = 0) ”
.

Definition OSMutexDel_full_entail_wit_12_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits (egrp_loop) (32)) = 0)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_full_entail_wit_13_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (mutex_del_abort_loop_missing_priotbl_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (mutex_del_abort_loop_missing_priotbl_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = (decode_PCP_from_cnt (ecnt_in))) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_full_entail_wit_13_1_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (mutex_del_abort_loop_missing_priotbl_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = (decode_PCP_from_cnt (ecnt_in))) ”
.

Definition OSMutexDel_full_entail_wit_13_1_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (((( &( "OSTCBPrioTbl" ) ) + ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) * sizeof(PTR)))) # Ptr  |-> 0)
  **  (mutex_del_abort_loop_missing_priotbl_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_full_entail_wit_13_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (255 = (decode_PCP_from_cnt (ecnt_in))) ”
  &&  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_full_entail_wit_13_2_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  “ (255 = (decode_PCP_from_cnt (ecnt_in))) ”
.

Definition OSMutexDel_full_entail_wit_13_2_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) = 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
.

Definition OSMutexDel_full_entail_wit_14 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v_2: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (tasks_v: Z) (current_tbl: (@list Z)) (owner_post: UCOS2_Verify_State) (current_event: OSEventAbstractState) (old_type: Z) (current: UCOS2_Verify_State) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg current )
  **  (mutex_del_pcp_release_focus sg ls0 current eid pcp_v )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> freelist_in)
  **  (used_event_wait_table_storage (current.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (owner_post) (current)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((current.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((current.(TskState) )) ((current.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v_2: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (tasks_v: Z) (current_tbl: (@list Z)) (owner_post: UCOS2_Verify_State) (current_event: OSEventAbstractState) (old_type: Z) (current: UCOS2_Verify_State) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg current )
  **  (mutex_del_pcp_release_focus sg ls0 current eid pcp_v )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> freelist_in)
  **  (used_event_wait_table_storage (current.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (owner_post) (current)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((current.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((current.(TskState) )) ((current.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
).

Definition OSMutexDel_full_entail_wit_14_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v_2: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (tasks_v: Z) (current_tbl: (@list Z)) (owner_post: UCOS2_Verify_State) (current_event: OSEventAbstractState) (old_type: Z) (current: UCOS2_Verify_State) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH3 : (pevent = (event_addr (sg) (eid)))) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (InsideCritical sg current )
  **  (mutex_del_pcp_release_focus sg ls0 current eid pcp_v )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> freelist_in)
  **  (used_event_wait_table_storage (current.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (owner_post) (current)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((current.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((current.(TskState) )) ((current.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v_2)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> pevent)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> 0)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
.

Definition OSMutexDel_full_entail_wit_15 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls2)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  EX (perr_v: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> perr_v)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls2)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
).

Definition OSMutexDel_full_entail_wit_15_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls2)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
.

Definition OSMutexDel_full_entail_wit_16_1 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (perr_v_2: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (critical_anchor: UCOS2_Verify_State) (ls_commit: UCOS2_Verify_State) (ls_exited: UCOS2_Verify_State) (ls_sched: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 1)) ,
  (OutsideCritical sg ls_sched )
  **  (mutex_del_transition_rep sg ls_exited ls_sched )
  **  (coq_prop (mutex_del_sched_stage_prop (ls_exited) (ls_sched)) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls_exited)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls_exited)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_v_2)
|--
  EX (perr_v: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> perr_v)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (critical_anchor: UCOS2_Verify_State) (ls_commit: UCOS2_Verify_State) (ls_exited: UCOS2_Verify_State) (ls_sched: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 1)) ,
  (OutsideCritical sg ls_sched )
  **  (mutex_del_transition_rep sg ls_exited ls_sched )
  **  (coq_prop (mutex_del_sched_stage_prop (ls_exited) (ls_sched)) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls_exited)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls_exited)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
).

Definition OSMutexDel_full_entail_wit_16_1_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (critical_anchor: UCOS2_Verify_State) (ls_commit: UCOS2_Verify_State) (ls_exited: UCOS2_Verify_State) (ls_sched: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 1)) ,
  (OutsideCritical sg ls_sched )
  **  (mutex_del_transition_rep sg ls_exited ls_sched )
  **  (coq_prop (mutex_del_sched_stage_prop (ls_exited) (ls_sched)) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls_exited)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls_exited)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
.

Definition OSMutexDel_full_entail_wit_16_2 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (perr_v_2: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) <> 1)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> perr_v_2)
|--
  EX (perr_v: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> perr_v)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) <> 1)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
).

Definition OSMutexDel_full_entail_wit_16_2_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) <> 1)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
.

Definition OSMutexDel_full_entail_wit_17 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (ls0) (ls0) (ls2)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  EX (perr_v: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 7 X )
  **  ((perr) # UChar  |-> perr_v)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (ls0) (ls0) (ls2)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 7 X )
).

Definition OSMutexDel_full_entail_wit_17_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls2: UCOS2_Verify_State) ,
  (OutsideCritical sg ls2 )
  **  (mutex_del_restore_rep false sg ls0 ls2 )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (ls0) (ls0) (ls2)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 7 X )
.

Definition OSMutexDel_full_entail_wit_18 := 
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (perr: Z) (pevent: Z) (tasks_waiting_addr_v: Z) (pevent_addr_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 <> opt_in)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent_addr_v) (tasks_waiting_addr_v)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent_addr_v) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent_addr_v opt_abs tasks_waiting_addr_v 7 X )
  **  ((perr) # UChar  |-> perr_in)
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (perr: Z) (pevent: Z) (tasks_waiting_addr_v: Z) (pevent_addr_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 <> opt_in)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent_addr_v) (tasks_waiting_addr_v)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent_addr_v) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent_addr_v opt_abs tasks_waiting_addr_v 7 X )
).

Definition OSMutexDel_full_entail_wit_18_split_goal_spatial := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (perr: Z) (pevent: Z) (tasks_waiting_addr_v: Z) (pevent_addr_v: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 <> opt_in)) ,
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent_addr_v) (tasks_waiting_addr_v)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent_addr_v) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent_addr_v opt_abs tasks_waiting_addr_v 7 X )
.

Definition OSMutexDel_full_return_wit_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_no_pend_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> 0)
|--
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = pe) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((perr_pre) # UChar  |-> 4)
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) ))
.

Definition OSMutexDel_full_return_wit_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
  **  ((perr) # UChar  |-> 73)
|--
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in <> 0) ” 
  &&  “ (opt_in <> 1) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 7))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 73))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr > 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 15))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 1))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((perr_pre) # UChar  |-> 4)
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) ))
.

Definition OSMutexDel_full_return_wit_3 := 
forall (perr_pre: Z) (pevent_pre: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_out_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> 0)
|--
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (0 = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (0 = pe) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((perr_pre) # UChar  |-> 4)
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) ))
.

Definition OSMutexDel_full_return_wit_4 := 
forall (perr_pre: Z) (pevent_pre: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_exit_inv sg e ls0 eid pevent opt_abs tasks_v 7 X )
  **  ((perr) # UChar  |-> 7)
|--
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 1) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (mutex_del_waiters_aborted_effective_prop (e) ((ls_post.(TskState) )) ((ls_post.(SchedState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  (coq_prop (prio_tbl_entry_prop ((ls_post.(TskState) )) ((decode_PCP_from_cnt (ecnt_in))) (PTFree)) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in = 0) ” 
  &&  “ ((decode_PCP_from_cnt (ecnt_in)) = 255) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (mutex_del_success_post_refinement_prop (sg) (e) (ls0) (eid) (opt_abs) (ls_post)) )
  **  (coq_prop (mutex_del_owner_restored_prop (e) ((ls_post.(TskState) ))) )
  **  ((perr_pre) # UChar  |-> 0))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in <> 0) ” 
  &&  “ (opt_in <> 1) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 7))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 73))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr > 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 15))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 1))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent = pe) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((perr_pre) # UChar  |-> 4)
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) ))
.

Definition OSMutexDel_full_return_wit_5 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : ((unsigned_last_nbits (isr) (32)) > 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (etype = 4)) (PreH6 : (pe = pevent_pre)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= etype)) (PreH10 : (etype <= 255)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (pe = pevent_pre)) (PreH15 : (pd = perr_pre)) (PreH16 : (opt_pre = opt_in)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH18 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH19 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 15)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pe = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in <> 0) ” 
  &&  “ (opt_in <> 1) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 7))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pe = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (opt_in = 0) ” 
  &&  “ (egrp_in <> 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 73))
  ||
  (EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pe = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype = 4) ” 
  &&  “ (isr > 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 15))
.

Definition OSMutexDel_full_return_wit_6 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype <> 4)) (PreH2 : (pe = pe)) (PreH3 : (pe = pevent_pre)) (PreH4 : (pe <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= etype)) (PreH7 : (etype <= 255)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (pe = pevent_pre)) (PreH12 : (pd = perr_pre)) (PreH13 : (opt_pre = opt_in)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH15 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH16 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 1)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pe = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 1)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype <> 4)) (PreH2 : (pe = pevent_pre)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= etype)) (PreH6 : (etype <= 255)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pe = pevent_pre)) (PreH11 : (pd = perr_pre)) (PreH12 : (opt_pre = opt_in)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH14 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH15 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (pe)) X ) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
).

Definition OSMutexDel_full_return_wit_7 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype <> 4)) (PreH2 : (pe = pe)) (PreH3 : (pe = pevent_pre)) (PreH4 : (pe <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= etype)) (PreH7 : (etype <= 255)) (PreH8 : (etype <> 4)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 1)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pe = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pe = pe) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr_pre) # UChar  |-> 1)
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype <> 4)) (PreH2 : (pe = pevent_pre)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= etype)) (PreH6 : (etype <= 255)) (PreH7 : (etype <> 4)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (pe = pevent_pre)) (PreH12 : (pd = perr_pre)) (PreH13 : (opt_pre = opt_in)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH15 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH16 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  EX (ls_post: UCOS2_Verify_State) ,
  “ (safeExec (LastSeen (ls_post)) (return (pe)) X ) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (etype <> 4) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_post.(TskState) )) ((ls_post.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
).

Definition OSMutexDel_full_return_wit_8 := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pe = pevent_pre)) (PreH5 : (pd = perr_pre)) (PreH6 : (opt_pre = opt_in)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH8 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((perr_pre) # UChar  |-> 4)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) )
|--
  EX (ls_post: UCOS2_Verify_State)  (retv: Z) ,
  “ (safeExec (LastSeen (ls_post)) (return (retv)) X ) ” 
  &&  “ (pevent_pre = retv) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (pevent_pre = pe) ” 
  &&  “ (pevent_pre = 0) ”
  &&  (OutsideCritical sg ls_post )
  **  (UCOS2_Verify_inv sg ls_post )
  **  ((perr_pre) # UChar  |-> 4)
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) )
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (ecnt_in: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pe = pevent_pre)) (PreH5 : (pd = perr_pre)) (PreH6 : (opt_pre = opt_in)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH8 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  TT && emp 
|--
  “ (safeExec (LastSeen (ls0)) (return (0)) X ) ”
  &&  emp
).

Definition OSMutexDel_full_return_wit_8_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (ecnt_in: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pe = pevent_pre)) (PreH5 : (pd = perr_pre)) (PreH6 : (opt_pre = opt_in)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH8 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (safeExec (LastSeen (ls0)) (return (0)) X )
.

Definition OSMutexDel_full_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pe = pevent_pre)) (PreH5 : (pd = perr_pre)) (PreH6 : (opt_pre = opt_in)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH8 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) )
|--
  “ (pe = pe) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ”
.

Definition OSMutexDel_full_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (pevent_pre <> 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (pe = pevent_pre)) (PreH5 : (pd = perr_pre)) (PreH6 : (opt_pre = opt_in)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH8 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
  **  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_pre) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) )
|--
  “ (pe = pe) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (opt_pre = opt_in) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X ) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pe) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt")) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  (UCOS2_Verify_inv sg ls0 )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
.

Definition OSMutexDel_full_partial_solve_wit_1 := OSMutexDel_full_partial_solve_wit_1_pure -> OSMutexDel_full_partial_solve_wit_1_aux.

Definition OSMutexDel_full_partial_solve_wit_2 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (pe = pe)) (PreH3 : (pe = pevent_pre)) (PreH4 : (pe <> 0)) (PreH5 : (pe = (event_addr (sg) (eid)))) (PreH6 : (0 <= etype)) (PreH7 : (etype <= 255)) (PreH8 : (pevent_pre <> 0)) (PreH9 : (perr_pre <> 0)) (PreH10 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH11 : (pe = pevent_pre)) (PreH12 : (pd = perr_pre)) (PreH13 : (opt_pre = opt_in)) (PreH14 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH15 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH16 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (etype = 4) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (opt_pre = opt_in) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X ) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
.

Definition OSMutexDel_full_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (pe = pevent_pre)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= etype)) (PreH6 : (etype <= 255)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pe = pevent_pre)) (PreH11 : (pd = perr_pre)) (PreH12 : (opt_pre = opt_in)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH14 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH15 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexDel_full_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (etype = 4)) (PreH2 : (pe = pevent_pre)) (PreH3 : (pe <> 0)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (0 <= etype)) (PreH6 : (etype <= 255)) (PreH7 : (pevent_pre <> 0)) (PreH8 : (perr_pre <> 0)) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (pe = pevent_pre)) (PreH11 : (pd = perr_pre)) (PreH12 : (opt_pre = opt_in)) (PreH13 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH14 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH15 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (opt_pre = opt_in) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X ) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
.

Definition OSMutexDel_full_partial_solve_wit_3 := OSMutexDel_full_partial_solve_wit_3_pure -> OSMutexDel_full_partial_solve_wit_3_aux.

Definition OSMutexDel_full_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pe = pevent_pre)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= etype)) (PreH8 : (etype <= 255)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 15)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexDel_full_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) > 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pe = pevent_pre)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= etype)) (PreH8 : (etype <= 255)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 15)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) > 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (opt_pre = opt_in) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X ) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 15)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
.

Definition OSMutexDel_full_partial_solve_wit_4 := OSMutexDel_full_partial_solve_wit_4_pure -> OSMutexDel_full_partial_solve_wit_4_aux.

Definition OSMutexDel_full_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : ((unsigned_last_nbits (isr) (32)) > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (etype = 4)) (PreH5 : (pe = pevent_pre)) (PreH6 : (pe <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= etype)) (PreH9 : (etype <= 255)) (PreH10 : (pevent_pre <> 0)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (pe = pevent_pre)) (PreH14 : (pd = perr_pre)) (PreH15 : (opt_pre = opt_in)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH17 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH18 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 15)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
.

Definition OSMutexDel_full_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : ((unsigned_last_nbits (isr) (32)) > 0)) (PreH3 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH4 : (etype = 4)) (PreH5 : (pe = pevent_pre)) (PreH6 : (pe <> 0)) (PreH7 : (pe = (event_addr (sg) (eid)))) (PreH8 : (0 <= etype)) (PreH9 : (etype <= 255)) (PreH10 : (pevent_pre <> 0)) (PreH11 : (perr_pre <> 0)) (PreH12 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH13 : (pe = pevent_pre)) (PreH14 : (pd = perr_pre)) (PreH15 : (opt_pre = opt_in)) (PreH16 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH17 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH18 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 15)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) > 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (opt_pre = opt_in) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X ) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> 15)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
.

Definition OSMutexDel_full_partial_solve_wit_5 := OSMutexDel_full_partial_solve_wit_5_pure -> OSMutexDel_full_partial_solve_wit_5_aux.

Definition OSMutexDel_full_partial_solve_wit_6_pure := 
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pe = pevent_pre)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= etype)) (PreH8 : (etype <= 255)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ”
) \/
(
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pe = pevent_pre)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= etype)) (PreH8 : (etype <= 255)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr <= 0) ”
).

Definition OSMutexDel_full_partial_solve_wit_6_pure_split_goal_1 := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pe = pevent_pre)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= etype)) (PreH8 : (etype <= 255)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr <= 0) ”
.

Definition OSMutexDel_full_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (etype = 4)) (PreH4 : (pe = pevent_pre)) (PreH5 : (pe <> 0)) (PreH6 : (pe = (event_addr (sg) (eid)))) (PreH7 : (0 <= etype)) (PreH8 : (etype <= 255)) (PreH9 : (pevent_pre <> 0)) (PreH10 : (perr_pre <> 0)) (PreH11 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH12 : (pe = pevent_pre)) (PreH13 : (pd = perr_pre)) (PreH14 : (opt_pre = opt_in)) (PreH15 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH16 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH17 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (opt_pre = opt_in) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X ) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
.

Definition OSMutexDel_full_partial_solve_wit_6 := OSMutexDel_full_partial_solve_wit_6_pure -> OSMutexDel_full_partial_solve_wit_6_aux.

Definition OSMutexDel_full_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (etype = 4)) (PreH6 : (pe = pevent_pre)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= etype)) (PreH10 : (etype <= 255)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (pe = pevent_pre)) (PreH15 : (pd = perr_pre)) (PreH16 : (opt_pre = opt_in)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH18 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH19 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pe)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "cpu_sr" ) )) # UInt  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "pcp" ) )) # UChar  |->_)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "tasks_waiting" ) )) # UChar  |->_)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ”
.

Definition OSMutexDel_full_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (opt_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : ((unsigned_last_nbits (isr) (32)) <= 0)) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (etype = 4)) (PreH6 : (pe = pevent_pre)) (PreH7 : (pe <> 0)) (PreH8 : (pe = (event_addr (sg) (eid)))) (PreH9 : (0 <= etype)) (PreH10 : (etype <= 255)) (PreH11 : (pevent_pre <> 0)) (PreH12 : (perr_pre <> 0)) (PreH13 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH14 : (pe = pevent_pre)) (PreH15 : (pd = perr_pre)) (PreH16 : (opt_pre = opt_in)) (PreH17 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X )) (PreH18 : (pcp_idx = (decode_PCP_from_cnt (ecnt_in)))) (PreH19 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((unsigned_last_nbits (isr) (32)) <= 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (pe = pevent_pre) ” 
  &&  “ (pd = perr_pre) ” 
  &&  “ (opt_pre = opt_in) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent_pre) (opt_abs))))) ((mutex_del_observe_ptr (pevent_pre)))) X ) ” 
  &&  “ (pcp_idx = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ”
  &&  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  (OutsideCritical sg ls0 )
.

Definition OSMutexDel_full_partial_solve_wit_7 := OSMutexDel_full_partial_solve_wit_7_pure -> OSMutexDel_full_partial_solve_wit_7_aux.

Definition OSMutexDel_full_partial_solve_wit_8 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) (PreH3 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH4 : (pe = (event_addr (sg) (eid)))) (PreH5 : (etype = 4)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((pd) # UChar  |-> perr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (OutsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (pe = (event_addr (sg) (eid))) ” 
  &&  “ (etype = 4) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pe) (opt_abs))))) ((mutex_del_observe_ptr (pe)))) X ) ”
  &&  (OutsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pe) (pd) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((pd) # UChar  |-> perr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pe)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pe e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventType")) (&((pe)  # "os_event" ->ₛ "OSEventPtr")) (&((pe)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pe)  # "os_event" ->ₛ "OSEventGrp")) (&((pe)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
.

Definition OSMutexDel_full_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (pevent = (event_addr (sg) (eid)))) (PreH8 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH9 : (owner_orig = (Z.land ecnt_in 255))) (PreH10 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH11 : (0 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ”
.

Definition OSMutexDel_full_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH4 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH5 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH6 : (isr <= 0)) (PreH7 : (pevent = (event_addr (sg) (eid)))) (PreH8 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH9 : (owner_orig = (Z.land ecnt_in 255))) (PreH10 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH11 : (0 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ ((unsigned_last_nbits (tasks_v) (32)) = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (0 = opt_in) ”
  &&  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_partial_solve_wit_9 := OSMutexDel_full_partial_solve_wit_9_pure -> OSMutexDel_full_partial_solve_wit_9_aux.

Definition OSMutexDel_full_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pevent = (event_addr (sg) (eid)))) (PreH10 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH11 : (owner_orig = (Z.land ecnt_in 255))) (PreH12 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH13 : (0 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ”
.

Definition OSMutexDel_full_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH6 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH7 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH8 : (isr <= 0)) (PreH9 : (pevent = (event_addr (sg) (eid)))) (PreH10 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH11 : (owner_orig = (Z.land ecnt_in 255))) (PreH12 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH13 : (0 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ ((unsigned_last_nbits (tasks_v) (32)) = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (0 = opt_in) ”
  &&  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_partial_solve_wit_10 := OSMutexDel_full_partial_solve_wit_10_pure -> OSMutexDel_full_partial_solve_wit_10_aux.

Definition OSMutexDel_full_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (eptr_in <> 0)) (PreH6 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH7 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (isr <= 0)) (PreH11 : (pevent = (event_addr (sg) (eid)))) (PreH12 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH13 : (owner_orig = (Z.land ecnt_in 255))) (PreH14 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH15 : (0 = opt_in)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ”
.

Definition OSMutexDel_full_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (eptr_in <> 0)) (PreH6 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH7 : ((unsigned_last_nbits (tasks_v) (32)) = 0)) (PreH8 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH9 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH10 : (isr <= 0)) (PreH11 : (pevent = (event_addr (sg) (eid)))) (PreH12 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH13 : (owner_orig = (Z.land ecnt_in 255))) (PreH14 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH15 : (0 = opt_in)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ ((unsigned_last_nbits (tasks_v) (32)) = 0) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (0 = opt_in) ”
  &&  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_partial_solve_wit_11 := OSMutexDel_full_partial_solve_wit_11_pure -> OSMutexDel_full_partial_solve_wit_11_aux.

Definition OSMutexDel_full_partial_solve_wit_12_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (ptcb_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pcp_v <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_v)
|--
  “ (pcp_v < 64) ” 
  &&  “ (0 <= pcp_v) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (ptcb_v: Z) (perr: Z) (pevent: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : (pcp_v <> 255)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_v)
|--
  “ (0 <= pcp_v) ” 
  &&  “ (pcp_v < 64) ”
).

Definition OSMutexDel_full_partial_solve_wit_12_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (ptcb_v: Z) (perr: Z) (pevent: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : (pcp_v <> 255)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_v)
|--
  “ (0 <= pcp_v) ”
.

Definition OSMutexDel_full_partial_solve_wit_12_pure_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (ptcb_v: Z) (perr: Z) (pevent: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : (pcp_v <> 255)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |-> prio_v)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_v)
|--
  “ (pcp_v < 64) ”
.

Definition OSMutexDel_full_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (prio_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pcp_v <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
|--
  “ (pcp_v < 64) ” 
  &&  “ (0 <= pcp_v) ” 
  &&  “ (pcp_v <> 255) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_v) (prio_v)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (0) (evtL_in)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_12 := OSMutexDel_full_partial_solve_wit_12_pure -> OSMutexDel_full_partial_solve_wit_12_aux.

Definition OSMutexDel_full_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
.

Definition OSMutexDel_full_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_13 := OSMutexDel_full_partial_solve_wit_13_pure -> OSMutexDel_full_partial_solve_wit_13_aux.

Definition OSMutexDel_full_partial_solve_wit_14 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_15 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_16 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_restore_rep false sg ls0 ls_commit )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_restore_rep false sg ls0 ls_commit )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_17 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
  **  ((perr) # UChar  |-> perr_in)
|--
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_v 73 X )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_18 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 <> opt_in)) (PreH11 : (1 = opt_in)) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ”
.

Definition OSMutexDel_full_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH4 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH5 : (isr <= 0)) (PreH6 : (pevent = (event_addr (sg) (eid)))) (PreH7 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH8 : (owner_orig = (Z.land ecnt_in 255))) (PreH9 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH10 : (0 <> opt_in)) (PreH11 : (1 = opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (0 <> opt_in) ” 
  &&  “ (1 = opt_in) ”
  &&  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_partial_solve_wit_19 := OSMutexDel_full_partial_solve_wit_19_pure -> OSMutexDel_full_partial_solve_wit_19_aux.

Definition OSMutexDel_full_partial_solve_wit_20_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pevent = (event_addr (sg) (eid)))) (PreH9 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH10 : (owner_orig = (Z.land ecnt_in 255))) (PreH11 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH12 : (0 <> opt_in)) (PreH13 : (1 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ”
.

Definition OSMutexDel_full_partial_solve_wit_20_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (eptr_in <> 0)) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH6 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH7 : (isr <= 0)) (PreH8 : (pevent = (event_addr (sg) (eid)))) (PreH9 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH10 : (owner_orig = (Z.land ecnt_in 255))) (PreH11 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH12 : (0 <> opt_in)) (PreH13 : (1 = opt_in)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (0 <> opt_in) ” 
  &&  “ (1 = opt_in) ”
  &&  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_partial_solve_wit_20 := OSMutexDel_full_partial_solve_wit_20_pure -> OSMutexDel_full_partial_solve_wit_20_aux.

Definition OSMutexDel_full_partial_solve_wit_21_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (eptr_in <> 0)) (PreH6 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (isr <= 0)) (PreH10 : (pevent = (event_addr (sg) (eid)))) (PreH11 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH12 : (owner_orig = (Z.land ecnt_in 255))) (PreH13 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH14 : (0 <> opt_in)) (PreH15 : (1 = opt_in)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "prio" ) )) # UChar  |-> (Z.land ecnt_in 255))
  **  ((( &( "ptcb" ) )) # Ptr  |-> eptr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ”
.

Definition OSMutexDel_full_partial_solve_wit_21_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH3 : (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH4 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH5 : (eptr_in <> 0)) (PreH6 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH7 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH8 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH9 : (isr <= 0)) (PreH10 : (pevent = (event_addr (sg) (eid)))) (PreH11 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH12 : (owner_orig = (Z.land ecnt_in 255))) (PreH13 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH14 : (0 <> opt_in)) (PreH15 : (1 = opt_in)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (owner_prio = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (eptr_in <> 0) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (0 <> opt_in) ” 
  &&  “ (1 = opt_in) ”
  &&  (InsideCritical sg ls0 )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_partial_solve_wit_21 := OSMutexDel_full_partial_solve_wit_21_pure -> OSMutexDel_full_partial_solve_wit_21_aux.

Definition OSMutexDel_full_partial_solve_wit_22_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp_v: Z) (cpu_sr_v: Z) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits (egrp_loop) (32)) <> 0)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (egrp_loop <> 0) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp_v: Z) (cpu_sr_v: Z) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : ((unsigned_last_nbits (egrp_loop) (32)) <> 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (egrp_loop <> 0) ”
).

Definition OSMutexDel_full_partial_solve_wit_22_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp_v: Z) (cpu_sr_v: Z) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : ((unsigned_last_nbits (egrp_loop) (32)) <> 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (egrp_loop <> 0) ”
.

Definition OSMutexDel_full_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (e_loop: OSEventAbstractState) (egrp_loop: Z) (evtL_loop: (@list Z)) (tasks_v: Z) (ls_owner_cur: UCOS2_Verify_State) (ls_loop: UCOS2_Verify_State) (pevent: Z) (perr: Z) (PreH1 : ((unsigned_last_nbits (egrp_loop) (32)) <> 0)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (egrp_loop <> 0) ” 
  &&  “ ((unsigned_last_nbits (egrp_loop) (32)) <> 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (InsideCritical sg ls_loop )
  **  (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls_loop.(TskState) )) ((ls_loop.(EventState) )) (eid) (e_loop) (4) (ecnt_in) (eptr_in) (egrp_loop) (evtL_loop)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_loop)
  **  (used_event_wait_table_storage (ls_loop.(TskState) ) pevent e_loop )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (ls_owner_cur)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (ls_owner_cur) (ls_loop)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls_loop.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
.

Definition OSMutexDel_full_partial_solve_wit_22 := OSMutexDel_full_partial_solve_wit_22_pure -> OSMutexDel_full_partial_solve_wit_22_aux.

Definition OSMutexDel_full_partial_solve_wit_23_pure := 
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) < 64) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ”
) \/
(
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) < 64) ”
).

Definition OSMutexDel_full_partial_solve_wit_23_pure_split_goal_1 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ (0 <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ”
.

Definition OSMutexDel_full_partial_solve_wit_23_pure_split_goal_2 := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (cpu_sr_v <= UINT_MAX)) (PreH2 : (cpu_sr_v >= 0)) (PreH3 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) < 64) ”
.

Definition OSMutexDel_full_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255)) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
|--
  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) < 64) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)) <> 255) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
.

Definition OSMutexDel_full_partial_solve_wit_23 := OSMutexDel_full_partial_solve_wit_23_pure -> OSMutexDel_full_partial_solve_wit_23_aux.

Definition OSMutexDel_full_partial_solve_wit_24_pure := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (cpu_sr_v: Z) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr_v)
  **  ((( &( "tasks_waiting" ) )) # UChar  |-> tasks_v)
  **  ((( &( "opt" ) )) # UChar  |-> opt_in)
  **  ((( &( "pevent_return" ) )) # Ptr  |->_)
  **  ((( &( "pcp" ) )) # UChar  |-> pcp_v)
  **  ((( &( "prio" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |->_)
  **  ((perr) # UChar  |-> perr_in)
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
.

Definition OSMutexDel_full_partial_solve_wit_24_aux := 
forall (perr_pre: Z) (pevent_pre: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pcp_v: Z) (perr: Z) (pevent: Z) (PreH1 : (pcp_v = (decode_PCP_from_cnt (ecnt_in)))) (PreH2 : (pevent = (event_addr (sg) (eid)))) (PreH3 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (pcp_v = (decode_PCP_from_cnt (ecnt_in))) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ”
  &&  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp_v freelist_in )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_24 := OSMutexDel_full_partial_solve_wit_24_pure -> OSMutexDel_full_partial_solve_wit_24_aux.

Definition OSMutexDel_full_partial_solve_wit_25 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_26 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_27 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (ls_commit: UCOS2_Verify_State) (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_restore_rep false sg ls0 ls_commit )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (InsideCritical sg critical_anchor )
  **  (mutex_del_restore_rep false sg ls0 ls_commit )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_28 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (perr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 1)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  ((perr) # UChar  |-> perr_v)
|--
  “ ((unsigned_last_nbits (tasks_v) (32)) = 1) ”
  &&  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_v X )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_v)
.

Definition OSMutexDel_full_partial_solve_wit_29 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (perr_v: Z) (tasks_v: Z) (perr: Z) (pevent: Z) (critical_anchor: UCOS2_Verify_State) (ls_commit: UCOS2_Verify_State) (ls_exited: UCOS2_Verify_State) (PreH1 : ((unsigned_last_nbits (tasks_v) (32)) = 1)) ,
  (OutsideCritical sg ls_exited )
  **  (mutex_del_transition_rep sg ls_exited ls_exited )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls_exited)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls_exited)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_v)
|--
  “ ((unsigned_last_nbits (tasks_v) (32)) = 1) ”
  &&  (OutsideCritical sg ls_exited )
  **  (mutex_del_transition_rep sg ls_exited ls_exited )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls_exited)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls_exited)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_v)
.

Definition OSMutexDel_full_partial_solve_wit_30 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_v) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_31 := 
forall (perr_pre: Z) (pevent_pre: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_v 7 X )
  **  ((perr) # UChar  |-> perr_in)
|--
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_v 7 X )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  ((perr) # UChar  |-> perr_in)
.

Definition OSMutexDel_full_partial_solve_wit_32 := 
forall (perr_pre: Z) (pevent_pre: Z) (prio_tbl_pcp: Z) (pcp_idx: Z) (prioL_in: (@list Z)) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (opt_in: Z) (perr_in: Z) (pd: Z) (pe: Z) (isr: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (perr: Z) (pevent: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) (PreH2 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH3 : (isr <= 0)) (PreH4 : (pevent = (event_addr (sg) (eid)))) (PreH5 : (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8)))) (PreH6 : (owner_orig = (Z.land ecnt_in 255))) (PreH7 : ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp)) (PreH8 : (0 <> opt_in)) (PreH9 : (1 <> opt_in)) ,
  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
|--
  “ (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X ) ” 
  &&  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ” 
  &&  “ (pevent = (event_addr (sg) (eid))) ” 
  &&  “ (pcp_idx = (unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ” 
  &&  “ (owner_orig = (Z.land ecnt_in 255)) ” 
  &&  “ ((Znth (pcp_idx) (prioL_in) (0)) = prio_tbl_pcp) ” 
  &&  “ (0 <> opt_in) ” 
  &&  “ (1 <> opt_in) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_return_lineage_prop (sg) (e) (ls0) (eid) (pe) (pd) (pevent) (perr) (pevent_pre) (perr_pre) (etype) (isr) (opt_in) (opt_abs) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (InsideCritical sg ls0 )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) ((unsigned_last_nbits ((Z.shiftr ecnt_in 8)) (8))) ((Z.land ecnt_in 255))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_option_decode_prop (opt_in) (opt_abs)) )
  **  ((perr) # UChar  |-> perr_in)
  **  (coq_prop (prio_tbl_list_rel (sg) ((ls0.(TskState) )) (prioL_in)) )
.

Definition OSMutexDel_full_which_implies_wit_1 := 
forall (pevent_pre: Z) (pcp_idx: Z) (owner_orig: Z) (owner_prio: Z) (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (etype: Z) (pe: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent_v: Z) (PreH1 : (pevent_v = pe)) (PreH2 : (pevent_v = pevent_pre)) (PreH3 : (pevent_v <> 0)) ,
  (coq_prop (mutex_del_input_classification_prop (sg) (ls0) (eid) (e) (pevent_v) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt")) (&((pevent_v)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_v)  # "os_event" ->ₛ "OSEventTbl")) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) (owner_orig) (pcp_idx)) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (UCOS2_Verify_inv sg ls0 )
|--
  (“ (pevent_v = pe) ” 
  &&  “ (pevent_v = pevent_pre) ” 
  &&  “ (pevent_v <> 0) ” 
  &&  “ (pevent_v = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ” 
  &&  “ (etype <> 4) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent_v e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_v)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) ))
  ||
  (“ (pevent_v = pe) ” 
  &&  “ (pevent_v = pevent_pre) ” 
  &&  “ (pevent_v <> 0) ” 
  &&  “ (pevent_v = (event_addr (sg) (eid))) ” 
  &&  “ (0 <= etype) ” 
  &&  “ (etype <= 255) ”
  &&  (coq_prop (valid_event_id (sg) (eid)) )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
  **  (coq_prop (mutex_del_owner_value_lineage_prop (e) (ecnt_in) (pcp_idx) (owner_orig)) )
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> etype)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent_v)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent_v e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (etype) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventType")) (&((pevent_v)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent_v)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent_v)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent_v)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) ))
.

Definition OSMutexDel_full_which_implies_wit_2 := 
(
forall (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_event_focus_inv sg ls0 eid )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
) \/
(
forall (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_event_focus_inv sg ls0 eid )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
).

Definition OSMutexDel_full_which_implies_wit_2_split_goal_spatial := 
forall (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) ,
  (mutex_del_event_focus_inv sg ls0 eid )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
.

Definition OSMutexDel_full_which_implies_wit_3 := 
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexDel_full_which_implies_wit_3_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
  **  (interrupt_inv sg (ls0.(IntrState) ) )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexDel_full_which_implies_wit_4 := 
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
  &&  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexDel_full_which_implies_wit_4_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexDel_full_which_implies_wit_5 := 
(
forall (isr: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ”
  &&  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexDel_full_which_implies_wit_5_split_goal_spatial := 
forall (isr: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexDel_full_which_implies_wit_6 := 
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ”
  &&  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexDel_full_which_implies_wit_6_split_goal_spatial := 
forall (isr: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> isr)
  **  (interrupt_inv_no_int_nesting sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexDel_full_which_implies_wit_7 := 
(
forall (isr: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  “ (isr = (intNesting ((ls0.(IntrState) )))) ” 
  &&  “ (isr <= 0) ”
  &&  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
) \/
(
forall (isr: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
).

Definition OSMutexDel_full_which_implies_wit_7_split_goal_spatial := 
forall (isr: Z) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (isr = (intNesting ((ls0.(IntrState) ))))) (PreH2 : (isr <= 0)) ,
  (interrupt_inv sg (ls0.(IntrState) ) )
  **  (mutex_del_event_focus_no_interrupt_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (os_int_nesting_addr (sg) (( &( "OSIntNesting" ) ))) )
.

Definition OSMutexDel_full_which_implies_wit_8 := 
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) (PreH3 : (eptr_in <> 0)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pcp <> 255) ”
  &&  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) (PreH3 : (eptr_in <> 0)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexDel_full_which_implies_wit_8_split_goal_spatial := 
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) (PreH3 : (eptr_in <> 0)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexDel_full_which_implies_wit_9 := 
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ (pcp <> 255) ”
  &&  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexDel_full_which_implies_wit_9_split_goal_spatial := 
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexDel_full_which_implies_wit_10 := 
(
forall (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (pevent: Z) (PreH1 : (0 <= pcp)) (PreH2 : (pcp < 64)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
|--
  EX (old_pcp_cell: Z)  (owner_post: UCOS2_Verify_State) ,
  (InsideCritical sg owner_post )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp * sizeof(PTR)))) # Ptr  |-> old_pcp_cell)
  **  (mutex_del_event_missing_priotbl_focus sg ls0 owner_post eid pcp )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (pevent: Z) (PreH1 : (0 <= pcp)) (PreH2 : (pcp < 64)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_owner_stage_focus sg e ls0 eid )
|--
  EX (old_pcp_cell: Z)  (owner_post: UCOS2_Verify_State) ,
  (InsideCritical sg owner_post )
  **  (((( &( "OSTCBPrioTbl" ) ) + (pcp * sizeof(PTR)))) # Ptr  |-> old_pcp_cell)
  **  (mutex_del_event_missing_priotbl_focus sg ls0 owner_post eid pcp )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_full_which_implies_wit_11 := 
(
forall (freelist_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pevent: Z) (pcp: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp freelist_in )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (current_tbl: (@list Z))  (current_event: OSEventAbstractState)  (old_type: Z)  (owner_post: UCOS2_Verify_State) ,
  “ (pcp = (decode_PCP_from_cnt (ecnt_in))) ”
  &&  (InsideCritical sg owner_post )
  **  (mutex_del_pcp_release_focus sg ls0 owner_post eid pcp )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> old_type)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (owner_post.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((owner_post.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((owner_post.(TskState) )) ((owner_post.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
) \/
(
forall (freelist_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pevent: Z) (pcp: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (mutex_del_no_pend_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp freelist_in )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (current_tbl: (@list Z))  (current_event: OSEventAbstractState)  (old_type: Z)  (owner_post: UCOS2_Verify_State) ,
  “ (pcp = (decode_PCP_from_cnt (ecnt_in))) ”
  &&  (InsideCritical sg owner_post )
  **  (mutex_del_pcp_release_focus sg ls0 owner_post eid pcp )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> old_type)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (owner_post.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((owner_post.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((owner_post.(TskState) )) ((owner_post.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_no_pend_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
).

Definition OSMutexDel_full_which_implies_wit_12 := 
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_waiting X )
|--
  EX (ls_commit: UCOS2_Verify_State)  (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_waiting)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
) \/
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_waiting X )
|--
  EX (ls_commit: UCOS2_Verify_State)  (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_waiting)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
).

Definition OSMutexDel_full_which_implies_wit_13 := 
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_waiting 73 X )
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_waiting) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
) \/
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_waiting 73 X )
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_waiting) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
).

Definition OSMutexDel_full_which_implies_wit_13_split_goal_spatial := 
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_waiting 73 X )
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_waiting) (73)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
.

Definition OSMutexDel_full_which_implies_wit_14 := 
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) (PreH3 : (eptr_in <> 0)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (pcp <> 255) ”
  &&  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) (PreH3 : (eptr_in <> 0)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexDel_full_which_implies_wit_14_split_goal_spatial := 
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) (PreH3 : (eptr_in <> 0)) ,
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexDel_full_which_implies_wit_15 := 
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  “ (eptr_in <> 0) ” 
  &&  “ (pcp <> 255) ”
  &&  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
) \/
(
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
).

Definition OSMutexDel_full_which_implies_wit_15_split_goal_spatial := 
forall (owner_prio: Z) (eptr_in: Z) (owner_t: TaskAbstractState) (owner_tid: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (PreH1 : (eptr_in <> 0)) (PreH2 : (pcp <> 255)) ,
  ((&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> owner_prio)
  **  (mutex_del_event_owner_open_inv sg ls0 eid owner_tid owner_t )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
|--
  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (mutex_del_owner_snapshot_prop (sg) (ls0) (e) (eptr_in) (owner_tid) (owner_t) (owner_prio) (&((eptr_in)  # "os_tcb" ->ₛ "OSTCBPrio"))) )
.

Definition OSMutexDel_full_which_implies_wit_16 := 
(
forall (freelist_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (pevent: Z) (PreH1 : (0 <= pcp)) (PreH2 : (pcp < 64)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
|--
  EX (old_pcp_cell: Z) ,
  (((( &( "OSTCBPrioTbl" ) ) + (pcp * sizeof(PTR)))) # Ptr  |-> old_pcp_cell)
  **  (mutex_del_abort_loop_missing_priotbl_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
) \/
(
forall (freelist_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pcp: Z) (pevent: Z) (PreH1 : (0 <= pcp)) (PreH2 : (pcp < 64)) ,
  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_abort_loop_residual sg e ls0 eid pevent ecnt_in eptr_in 0 freelist_in )
|--
  EX (old_pcp_cell: Z) ,
  (((( &( "OSTCBPrioTbl" ) ) + (pcp * sizeof(PTR)))) # Ptr  |-> old_pcp_cell)
  **  (mutex_del_abort_loop_missing_priotbl_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp freelist_in )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (os_tcb_prio_tbl_addr (sg) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
).

Definition OSMutexDel_full_which_implies_wit_17 := 
(
forall (freelist_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pevent: Z) (pcp: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp freelist_in )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (current_tbl: (@list Z))  (owner_post: UCOS2_Verify_State)  (current_event: OSEventAbstractState)  (old_type: Z)  (current: UCOS2_Verify_State) ,
  “ (pcp = (decode_PCP_from_cnt (ecnt_in))) ”
  &&  (InsideCritical sg current )
  **  (mutex_del_pcp_release_focus sg ls0 current eid pcp )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> old_type)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (current.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (owner_post) (current)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((current.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((current.(TskState) )) ((current.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
) \/
(
forall (freelist_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_v: Z) (pevent: Z) (pcp: Z) (PreH1 : (safeExec (LastSeen (ls0)) (bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent)))) X )) ,
  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (mutex_del_abort_loop_pcp_release_residual sg e ls0 eid pevent ecnt_in eptr_in 0 pcp freelist_in )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
|--
  EX (current_tbl: (@list Z))  (owner_post: UCOS2_Verify_State)  (current_event: OSEventAbstractState)  (old_type: Z)  (current: UCOS2_Verify_State) ,
  “ (pcp = (decode_PCP_from_cnt (ecnt_in))) ”
  &&  (InsideCritical sg current )
  **  (mutex_del_pcp_release_focus sg ls0 current eid pcp )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> old_type)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  (used_event_wait_table_storage (current.(TskState) ) pevent current_event )
  **  (coq_prop (mutex_del_rdyatprio_stage_prop (sg) (e) (ls0) (owner_post)) )
  **  (coq_prop (mutex_del_wake_steps (sg) (eid) (owner_post) (current)) )
  **  (coq_prop (event_free_list_head_prop (sg) ((current.(EventState) )) (freelist_in)) )
  **  (coq_prop (event_snapshot_of_prop (sg) ((current.(TskState) )) ((current.(EventState) )) (eid) (current_event) (old_type) (ecnt_in) (eptr_in) (0) (current_tbl)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_v)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (mutex_del_always_mode_prop (opt_abs) (tasks_v)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
).

Definition OSMutexDel_full_which_implies_wit_18 := 
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_waiting X )
|--
  EX (ls_commit: UCOS2_Verify_State)  (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_waiting)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
) \/
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (mutex_del_success_commit_inv sg e ls0 eid opt_abs pevent tasks_waiting X )
|--
  EX (ls_commit: UCOS2_Verify_State)  (critical_anchor: UCOS2_Verify_State) ,
  (InsideCritical sg critical_anchor )
  **  (mutex_del_transition_rep sg ls0 ls_commit )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_waiting)) )
  **  (coq_prop (mutex_del_refresh_context_prop (sg) (( &( "OSRdyGrp" ) )) (( &( "OSRdyTbl" ) )) (( &( "OSPrioHighRdy" ) )) (( &( "OSTCBHighRdy" ) )) (( &( "OSTCBPrioTbl" ) ))) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
).

Definition OSMutexDel_full_which_implies_wit_19 := 
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_waiting X )
|--
  EX (critical_anchor: UCOS2_Verify_State)  (ls_commit: UCOS2_Verify_State)  (ls_exited: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_exited )
  **  (mutex_del_transition_rep sg ls_exited ls_exited )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_waiting)) )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls_exited)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls_exited)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
) \/
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_success_exit_inv sg e ls0 eid opt_abs pevent tasks_waiting X )
|--
  EX (critical_anchor: UCOS2_Verify_State)  (ls_commit: UCOS2_Verify_State)  (ls_exited: UCOS2_Verify_State) ,
  (OutsideCritical sg ls_exited )
  **  (mutex_del_transition_rep sg ls_exited ls_exited )
  **  (coq_prop (mutex_del_success_commit_anchor_prop (sg) (e) (ls0) (eid) (opt_abs) (critical_anchor) (ls_commit)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_success_mode_prop (opt_abs) (tasks_waiting)) )
  **  (coq_prop (mutex_del_exit_critical_anchored_call_prop (sg) (critical_anchor) (ls_commit) (ls_exited)) )
  **  (coq_prop (UCOS2_validity_bundle (sg) (ls_exited)) )
  **  (coq_prop (valid_stable_glob_vars (sg)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
).

Definition OSMutexDel_full_which_implies_wit_20 := 
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_waiting 7 X )
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_waiting) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
) \/
(
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_waiting 7 X )
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_waiting) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
).

Definition OSMutexDel_full_which_implies_wit_20_split_goal_spatial := 
forall (e: OSEventAbstractState) (eid: Z) (opt_abs: MutexDelOpt) (X: (Z -> ((UCOS2_Verify_State -> Prop) -> Prop))) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (tasks_waiting: Z) (pevent: Z) ,
  (mutex_del_unchanged_inside_inv sg e ls0 eid pevent opt_abs tasks_waiting 7 X )
|--
  (InsideCritical sg ls0 )
  **  (mutex_del_restore_rep false sg ls0 ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
  **  (coq_prop (mutex_del_error_mode_prop (opt_abs) (tasks_waiting) (7)) )
  **  (coq_prop (safeExec ((LastSeen (ls0))) ((bind ((atomic_cmd ((OSMutexDel_full_sem (sg) (pevent) (opt_abs))))) ((mutex_del_observe_ptr (pevent))))) (X)) )
.

Definition OSMutexDel_full_which_implies_wit_21 := 
(
forall (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (tasks_waiting: Z) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
|--
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
) \/
(
forall (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (tasks_waiting: Z) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
|--
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
).

Definition OSMutexDel_full_which_implies_wit_21_split_goal_spatial := 
forall (freelist_in: Z) (evtL_in: (@list Z)) (egrp_in: Z) (eptr_in: Z) (ecnt_in: Z) (e: OSEventAbstractState) (eid: Z) (ls0: UCOS2_Verify_State) (sg: StableGlobVars) (pevent: Z) (tasks_waiting: Z) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 4)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> eptr_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventCnt")) # UShort  |-> ecnt_in)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> egrp_in)
  **  (used_event_wait_table_storage (ls0.(TskState) ) pevent e )
  **  ((( &( "OSEventFreeList" ) )) # Ptr  |-> freelist_in)
  **  (mutex_del_event_focus_inv sg ls0 eid )
  **  (coq_prop (event_snapshot_of_prop (sg) ((ls0.(TskState) )) ((ls0.(EventState) )) (eid) (e) (4) (ecnt_in) (eptr_in) (egrp_in) (evtL_in)) )
  **  (coq_prop (event_core_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventType")) (&((pevent)  # "os_event" ->ₛ "OSEventPtr")) (&((pevent)  # "os_event" ->ₛ "OSEventCnt"))) )
  **  (coq_prop (event_wait_fields_layout_prop (sg) (eid) (&((pevent)  # "os_event" ->ₛ "OSEventGrp")) (&((pevent)  # "os_event" ->ₛ "OSEventTbl"))) )
  **  (coq_prop (os_event_free_list_addr (sg) (( &( "OSEventFreeList" ) ))) )
  **  (coq_prop (event_free_list_head_prop (sg) ((ls0.(EventState) )) (freelist_in)) )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
|--
  (UCOS2_Verify_inv sg ls0 )
  **  (coq_prop (mutex_del_source_entry_prop (sg) (e) (ls0) (eid) (pevent) (tasks_waiting)) )
.

Module Type VC_Correct.


Axiom proof_of_OSMutexDel_FirstSet8_return_wit_1 : OSMutexDel_FirstSet8_return_wit_1.
Axiom proof_of_OSMutexDel_FirstSet8_return_wit_2 : OSMutexDel_FirstSet8_return_wit_2.
Axiom proof_of_OSMutexDel_FirstSet8_return_wit_3 : OSMutexDel_FirstSet8_return_wit_3.
Axiom proof_of_OSMutexDel_FirstSet8_return_wit_4 : OSMutexDel_FirstSet8_return_wit_4.
Axiom proof_of_OSMutexDel_FirstSet8_return_wit_5 : OSMutexDel_FirstSet8_return_wit_5.
Axiom proof_of_OSMutexDel_FirstSet8_return_wit_6 : OSMutexDel_FirstSet8_return_wit_6.
Axiom proof_of_OSMutexDel_FirstSet8_return_wit_7 : OSMutexDel_FirstSet8_return_wit_7.
Axiom proof_of_OSMutexDel_FirstSet8_return_wit_8 : OSMutexDel_FirstSet8_return_wit_8.
Axiom proof_of_OSMutexDel_RefreshHighReady_safety_wit_1 : OSMutexDel_RefreshHighReady_safety_wit_1.
Axiom proof_of_OSMutexDel_RefreshHighReady_return_wit_1 : OSMutexDel_RefreshHighReady_return_wit_1.
Axiom proof_of_OSMutexDel_RefreshHighReady_return_wit_2 : OSMutexDel_RefreshHighReady_return_wit_2.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_1 : OSMutexDel_RefreshHighReady_partial_solve_wit_1.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_2_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_2_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_2 : OSMutexDel_RefreshHighReady_partial_solve_wit_2.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_3 : OSMutexDel_RefreshHighReady_partial_solve_wit_3.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_4 : OSMutexDel_RefreshHighReady_partial_solve_wit_4.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_5 : OSMutexDel_RefreshHighReady_partial_solve_wit_5.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_6_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_6_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_6 : OSMutexDel_RefreshHighReady_partial_solve_wit_6.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_7_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_7_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_7 : OSMutexDel_RefreshHighReady_partial_solve_wit_7.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_8 : OSMutexDel_RefreshHighReady_partial_solve_wit_8.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_9_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_9_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_9 : OSMutexDel_RefreshHighReady_partial_solve_wit_9.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_10_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_10_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_10 : OSMutexDel_RefreshHighReady_partial_solve_wit_10.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_11_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_11_pure.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_11 : OSMutexDel_RefreshHighReady_partial_solve_wit_11.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_12 : OSMutexDel_RefreshHighReady_partial_solve_wit_12.
Axiom proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_13 : OSMutexDel_RefreshHighReady_partial_solve_wit_13.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_1 : OSMutexDel_RefreshHighReady_which_implies_wit_1.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_2 : OSMutexDel_RefreshHighReady_which_implies_wit_2.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_3 : OSMutexDel_RefreshHighReady_which_implies_wit_3.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_4 : OSMutexDel_RefreshHighReady_which_implies_wit_4.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_5 : OSMutexDel_RefreshHighReady_which_implies_wit_5.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_6 : OSMutexDel_RefreshHighReady_which_implies_wit_6.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_7 : OSMutexDel_RefreshHighReady_which_implies_wit_7.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_8 : OSMutexDel_RefreshHighReady_which_implies_wit_8.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_9 : OSMutexDel_RefreshHighReady_which_implies_wit_9.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_10 : OSMutexDel_RefreshHighReady_which_implies_wit_10.
Axiom proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_11 : OSMutexDel_RefreshHighReady_which_implies_wit_11.
Axiom proof_of_OSMutexDel_full_safety_wit_1 : OSMutexDel_full_safety_wit_1.
Axiom proof_of_OSMutexDel_full_safety_wit_2 : OSMutexDel_full_safety_wit_2.
Axiom proof_of_OSMutexDel_full_safety_wit_3 : OSMutexDel_full_safety_wit_3.
Axiom proof_of_OSMutexDel_full_safety_wit_4 : OSMutexDel_full_safety_wit_4.
Axiom proof_of_OSMutexDel_full_safety_wit_5 : OSMutexDel_full_safety_wit_5.
Axiom proof_of_OSMutexDel_full_safety_wit_6 : OSMutexDel_full_safety_wit_6.
Axiom proof_of_OSMutexDel_full_safety_wit_7 : OSMutexDel_full_safety_wit_7.
Axiom proof_of_OSMutexDel_full_safety_wit_8 : OSMutexDel_full_safety_wit_8.
Axiom proof_of_OSMutexDel_full_safety_wit_9 : OSMutexDel_full_safety_wit_9.
Axiom proof_of_OSMutexDel_full_safety_wit_10 : OSMutexDel_full_safety_wit_10.
Axiom proof_of_OSMutexDel_full_safety_wit_11 : OSMutexDel_full_safety_wit_11.
Axiom proof_of_OSMutexDel_full_safety_wit_12 : OSMutexDel_full_safety_wit_12.
Axiom proof_of_OSMutexDel_full_entail_wit_1 : OSMutexDel_full_entail_wit_1.
Axiom proof_of_OSMutexDel_full_entail_wit_2_1 : OSMutexDel_full_entail_wit_2_1.
Axiom proof_of_OSMutexDel_full_entail_wit_2_2 : OSMutexDel_full_entail_wit_2_2.
Axiom proof_of_OSMutexDel_full_entail_wit_3_1 : OSMutexDel_full_entail_wit_3_1.
Axiom proof_of_OSMutexDel_full_entail_wit_3_2 : OSMutexDel_full_entail_wit_3_2.
Axiom proof_of_OSMutexDel_full_entail_wit_3_3 : OSMutexDel_full_entail_wit_3_3.
Axiom proof_of_OSMutexDel_full_entail_wit_4_1 : OSMutexDel_full_entail_wit_4_1.
Axiom proof_of_OSMutexDel_full_entail_wit_4_2 : OSMutexDel_full_entail_wit_4_2.
Axiom proof_of_OSMutexDel_full_entail_wit_5 : OSMutexDel_full_entail_wit_5.
Axiom proof_of_OSMutexDel_full_entail_wit_6 : OSMutexDel_full_entail_wit_6.
Axiom proof_of_OSMutexDel_full_entail_wit_7 : OSMutexDel_full_entail_wit_7.
Axiom proof_of_OSMutexDel_full_entail_wit_8 : OSMutexDel_full_entail_wit_8.
Axiom proof_of_OSMutexDel_full_entail_wit_9_1 : OSMutexDel_full_entail_wit_9_1.
Axiom proof_of_OSMutexDel_full_entail_wit_9_2 : OSMutexDel_full_entail_wit_9_2.
Axiom proof_of_OSMutexDel_full_entail_wit_9_3 : OSMutexDel_full_entail_wit_9_3.
Axiom proof_of_OSMutexDel_full_entail_wit_9_4 : OSMutexDel_full_entail_wit_9_4.
Axiom proof_of_OSMutexDel_full_entail_wit_10 : OSMutexDel_full_entail_wit_10.
Axiom proof_of_OSMutexDel_full_entail_wit_11 : OSMutexDel_full_entail_wit_11.
Axiom proof_of_OSMutexDel_full_entail_wit_12 : OSMutexDel_full_entail_wit_12.
Axiom proof_of_OSMutexDel_full_entail_wit_13_1 : OSMutexDel_full_entail_wit_13_1.
Axiom proof_of_OSMutexDel_full_entail_wit_13_2 : OSMutexDel_full_entail_wit_13_2.
Axiom proof_of_OSMutexDel_full_entail_wit_14 : OSMutexDel_full_entail_wit_14.
Axiom proof_of_OSMutexDel_full_entail_wit_15 : OSMutexDel_full_entail_wit_15.
Axiom proof_of_OSMutexDel_full_entail_wit_16_1 : OSMutexDel_full_entail_wit_16_1.
Axiom proof_of_OSMutexDel_full_entail_wit_16_2 : OSMutexDel_full_entail_wit_16_2.
Axiom proof_of_OSMutexDel_full_entail_wit_17 : OSMutexDel_full_entail_wit_17.
Axiom proof_of_OSMutexDel_full_entail_wit_18 : OSMutexDel_full_entail_wit_18.
Axiom proof_of_OSMutexDel_full_return_wit_1 : OSMutexDel_full_return_wit_1.
Axiom proof_of_OSMutexDel_full_return_wit_2 : OSMutexDel_full_return_wit_2.
Axiom proof_of_OSMutexDel_full_return_wit_3 : OSMutexDel_full_return_wit_3.
Axiom proof_of_OSMutexDel_full_return_wit_4 : OSMutexDel_full_return_wit_4.
Axiom proof_of_OSMutexDel_full_return_wit_5 : OSMutexDel_full_return_wit_5.
Axiom proof_of_OSMutexDel_full_return_wit_6 : OSMutexDel_full_return_wit_6.
Axiom proof_of_OSMutexDel_full_return_wit_7 : OSMutexDel_full_return_wit_7.
Axiom proof_of_OSMutexDel_full_return_wit_8 : OSMutexDel_full_return_wit_8.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_1_pure : OSMutexDel_full_partial_solve_wit_1_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_1 : OSMutexDel_full_partial_solve_wit_1.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_2 : OSMutexDel_full_partial_solve_wit_2.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_3_pure : OSMutexDel_full_partial_solve_wit_3_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_3 : OSMutexDel_full_partial_solve_wit_3.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_4_pure : OSMutexDel_full_partial_solve_wit_4_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_4 : OSMutexDel_full_partial_solve_wit_4.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_5_pure : OSMutexDel_full_partial_solve_wit_5_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_5 : OSMutexDel_full_partial_solve_wit_5.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_6_pure : OSMutexDel_full_partial_solve_wit_6_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_6 : OSMutexDel_full_partial_solve_wit_6.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_7_pure : OSMutexDel_full_partial_solve_wit_7_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_7 : OSMutexDel_full_partial_solve_wit_7.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_8 : OSMutexDel_full_partial_solve_wit_8.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_9_pure : OSMutexDel_full_partial_solve_wit_9_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_9 : OSMutexDel_full_partial_solve_wit_9.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_10_pure : OSMutexDel_full_partial_solve_wit_10_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_10 : OSMutexDel_full_partial_solve_wit_10.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_11_pure : OSMutexDel_full_partial_solve_wit_11_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_11 : OSMutexDel_full_partial_solve_wit_11.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_12_pure : OSMutexDel_full_partial_solve_wit_12_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_12 : OSMutexDel_full_partial_solve_wit_12.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_13_pure : OSMutexDel_full_partial_solve_wit_13_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_13 : OSMutexDel_full_partial_solve_wit_13.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_14 : OSMutexDel_full_partial_solve_wit_14.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_15 : OSMutexDel_full_partial_solve_wit_15.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_16 : OSMutexDel_full_partial_solve_wit_16.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_17 : OSMutexDel_full_partial_solve_wit_17.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_18 : OSMutexDel_full_partial_solve_wit_18.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_19_pure : OSMutexDel_full_partial_solve_wit_19_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_19 : OSMutexDel_full_partial_solve_wit_19.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_20_pure : OSMutexDel_full_partial_solve_wit_20_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_20 : OSMutexDel_full_partial_solve_wit_20.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_21_pure : OSMutexDel_full_partial_solve_wit_21_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_21 : OSMutexDel_full_partial_solve_wit_21.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_22_pure : OSMutexDel_full_partial_solve_wit_22_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_22 : OSMutexDel_full_partial_solve_wit_22.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_23_pure : OSMutexDel_full_partial_solve_wit_23_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_23 : OSMutexDel_full_partial_solve_wit_23.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_24_pure : OSMutexDel_full_partial_solve_wit_24_pure.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_24 : OSMutexDel_full_partial_solve_wit_24.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_25 : OSMutexDel_full_partial_solve_wit_25.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_26 : OSMutexDel_full_partial_solve_wit_26.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_27 : OSMutexDel_full_partial_solve_wit_27.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_28 : OSMutexDel_full_partial_solve_wit_28.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_29 : OSMutexDel_full_partial_solve_wit_29.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_30 : OSMutexDel_full_partial_solve_wit_30.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_31 : OSMutexDel_full_partial_solve_wit_31.
Axiom proof_of_OSMutexDel_full_partial_solve_wit_32 : OSMutexDel_full_partial_solve_wit_32.
Axiom proof_of_OSMutexDel_full_which_implies_wit_1 : OSMutexDel_full_which_implies_wit_1.
Axiom proof_of_OSMutexDel_full_which_implies_wit_2 : OSMutexDel_full_which_implies_wit_2.
Axiom proof_of_OSMutexDel_full_which_implies_wit_3 : OSMutexDel_full_which_implies_wit_3.
Axiom proof_of_OSMutexDel_full_which_implies_wit_4 : OSMutexDel_full_which_implies_wit_4.
Axiom proof_of_OSMutexDel_full_which_implies_wit_5 : OSMutexDel_full_which_implies_wit_5.
Axiom proof_of_OSMutexDel_full_which_implies_wit_6 : OSMutexDel_full_which_implies_wit_6.
Axiom proof_of_OSMutexDel_full_which_implies_wit_7 : OSMutexDel_full_which_implies_wit_7.
Axiom proof_of_OSMutexDel_full_which_implies_wit_8 : OSMutexDel_full_which_implies_wit_8.
Axiom proof_of_OSMutexDel_full_which_implies_wit_9 : OSMutexDel_full_which_implies_wit_9.
Axiom proof_of_OSMutexDel_full_which_implies_wit_10 : OSMutexDel_full_which_implies_wit_10.
Axiom proof_of_OSMutexDel_full_which_implies_wit_11 : OSMutexDel_full_which_implies_wit_11.
Axiom proof_of_OSMutexDel_full_which_implies_wit_12 : OSMutexDel_full_which_implies_wit_12.
Axiom proof_of_OSMutexDel_full_which_implies_wit_13 : OSMutexDel_full_which_implies_wit_13.
Axiom proof_of_OSMutexDel_full_which_implies_wit_14 : OSMutexDel_full_which_implies_wit_14.
Axiom proof_of_OSMutexDel_full_which_implies_wit_15 : OSMutexDel_full_which_implies_wit_15.
Axiom proof_of_OSMutexDel_full_which_implies_wit_16 : OSMutexDel_full_which_implies_wit_16.
Axiom proof_of_OSMutexDel_full_which_implies_wit_17 : OSMutexDel_full_which_implies_wit_17.
Axiom proof_of_OSMutexDel_full_which_implies_wit_18 : OSMutexDel_full_which_implies_wit_18.
Axiom proof_of_OSMutexDel_full_which_implies_wit_19 : OSMutexDel_full_which_implies_wit_19.
Axiom proof_of_OSMutexDel_full_which_implies_wit_20 : OSMutexDel_full_which_implies_wit_20.
Axiom proof_of_OSMutexDel_full_which_implies_wit_21 : OSMutexDel_full_which_implies_wit_21.

End VC_Correct.
