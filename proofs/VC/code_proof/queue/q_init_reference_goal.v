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
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_source_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_reference_layout.
Local Open Scope sac.

(*----- Function OS_QInit -----*)

Definition OS_QInit_safety_wit_1 := 
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_QInit_safety_wit_2 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") )) (PreH8 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH9 : (valid_stable_glob_vars sg )) (PreH10 : (queue_first_round_profile sg )) (PreH11 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_last_link_residual sg )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_QInit_safety_wit_3 := 
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (3 = 3)) (PreH7 : ((( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) (PreH8 : (valid_stable_glob_vars sg )) (PreH9 : (queue_first_round_profile sg )) (PreH10 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH11 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH12 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH13 : (ix = 3)) (PreH14 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  ((( &( "ix" ) )) # UShort  |-> 3)
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))
  **  ((( &( "OSQFreeList" ) )) # Ptr  |->_)
  **  (q_init_publish_residual sg )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_QInit_entail_wit_1 := 
(
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (q_init_after_clear sg )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ”
  &&  (q_init_loop_state sg 0 )
) \/
(
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (q_init_after_clear sg )
|--
  (q_init_loop_state sg 0 )
).

Definition OS_QInit_entail_wit_1_split_goal_spatial := 
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (q_init_after_clear sg )
|--
  (q_init_loop_state sg 0 )
.

Definition OS_QInit_entail_wit_2 := 
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : ((ix + 1 ) = (ix + 1 ))) (PreH7 : ((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))) (PreH8 : ((( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))))) (PreH9 : (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") )) (PreH10 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH11 : (valid_stable_glob_vars sg )) (PreH12 : (queue_first_round_profile sg )) (PreH13 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH14 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH15 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))))
  **  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))))
  **  (q_init_loop_residual sg ix )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ”
  &&  (q_init_link_committed sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
) \/
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") )) (PreH7 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH8 : (valid_stable_glob_vars sg )) (PreH9 : (queue_first_round_profile sg )) (PreH10 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH11 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH12 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))))
  **  (q_init_loop_residual sg ix )
|--
  (q_init_link_committed sg ix )
).

Definition OS_QInit_entail_wit_2_split_goal_spatial := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") )) (PreH7 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH8 : (valid_stable_glob_vars sg )) (PreH9 : (queue_first_round_profile sg )) (PreH10 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH11 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH12 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))))
  **  (q_init_loop_residual sg ix )
|--
  (q_init_link_committed sg ix )
.

Definition OS_QInit_entail_wit_3 := 
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  (q_init_link_committed sg ix )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ”
  &&  (q_init_loop_state sg (unsigned_last_nbits ((ix + 1 )) (16)) )
) \/
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  (q_init_link_committed sg ix )
|--
  (q_init_loop_state sg (unsigned_last_nbits ((ix + 1 )) (16)) )
).

Definition OS_QInit_entail_wit_3_split_goal_spatial := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  (q_init_link_committed sg ix )
|--
  (q_init_loop_state sg (unsigned_last_nbits ((ix + 1 )) (16)) )
.

Definition OS_QInit_entail_wit_4 := 
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") )) (PreH8 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH9 : (valid_stable_glob_vars sg )) (PreH10 : (queue_first_round_profile sg )) (PreH11 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_last_link_residual sg )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix = 3) ” 
  &&  “ ((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" )))) ”
  &&  (q_init_before_publish sg )
) \/
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") )) (PreH8 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH9 : (valid_stable_glob_vars sg )) (PreH10 : (queue_first_round_profile sg )) (PreH11 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_last_link_residual sg )
|--
  (q_init_before_publish sg )
).

Definition OS_QInit_entail_wit_4_split_goal_spatial := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") )) (PreH8 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH9 : (valid_stable_glob_vars sg )) (PreH10 : (queue_first_round_profile sg )) (PreH11 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH12 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH13 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_last_link_residual sg )
|--
  (q_init_before_publish sg )
.

Definition OS_QInit_return_wit_1 := 
(
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (3 = 3)) (PreH7 : ((( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) (PreH8 : (valid_stable_glob_vars sg )) (PreH9 : (queue_first_round_profile sg )) (PreH10 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH11 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH12 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH13 : (ix = 3)) (PreH14 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  ((( &( "OSQFreeList" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))))
  **  (q_init_publish_residual sg )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ”
  &&  (OS_QInit_spec sg )
) \/
(
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (valid_stable_glob_vars sg )) (PreH7 : (queue_first_round_profile sg )) (PreH8 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH9 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH10 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH11 : (ix = 3)) (PreH12 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  ((( &( "OSQFreeList" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))))
  **  (q_init_publish_residual sg )
|--
  (OS_QInit_spec sg )
).

Definition OS_QInit_return_wit_1_split_goal_spatial := 
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (valid_stable_glob_vars sg )) (PreH7 : (queue_first_round_profile sg )) (PreH8 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH9 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH10 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH11 : (ix = 3)) (PreH12 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  ((( &( "OSQFreeList" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))))
  **  (q_init_publish_residual sg )
|--
  (OS_QInit_spec sg )
.

Definition OS_QInit_partial_solve_wit_1_pure := 
forall (sg: StableGlobVars) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (q_init_zynq7_reference_layout sg )) ,
  ((( &( "pq2" ) )) # Ptr  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (queue_init_pre sg )
|--
  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ”
.

Definition OS_QInit_partial_solve_wit_1_aux := 
forall (sg: StableGlobVars) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (q_init_zynq7_reference_layout sg )) ,
  (queue_init_pre sg )
|--
  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_zynq7_reference_layout sg ) ”
  &&  (queue_init_pre sg )
.

Definition OS_QInit_partial_solve_wit_1 := OS_QInit_partial_solve_wit_1_pure -> OS_QInit_partial_solve_wit_1_aux.

Definition OS_QInit_partial_solve_wit_2_pure := 
(
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= (sizeof( "os_q" ) * 4)) ” 
  &&  “ ((sizeof( "os_q" ) * 4) <= 65535) ” 
  &&  “ (((( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) + ((sizeof( "os_q" ) * 4) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" )))) ”
) \/
(
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" )))) ” 
  &&  “ (((( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) + ((sizeof( "os_q" ) * 4) * sizeof(UCHAR))) <= UINT_MAX) ”
).

Definition OS_QInit_partial_solve_wit_2_pure_split_goal_1 := 
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" )))) ”
.

Definition OS_QInit_partial_solve_wit_2_pure_split_goal_2 := 
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (((( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) + ((sizeof( "os_q" ) * 4) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_QInit_partial_solve_wit_2_aux := 
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
|--
  “ (0 <= (sizeof( "os_q" ) * 4)) ” 
  &&  “ ((sizeof( "os_q" ) * 4) <= 65535) ” 
  &&  “ (((( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) + ((sizeof( "os_q" ) * 4) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" )))) ” 
  &&  “ (((g_OSQTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (0 <= (g_OSQTbl (sg))) ” 
  &&  “ (((g_OSQTbl (sg)) + 96 ) <= 4294967296) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_zynq7_reference_layout sg ) ”
  &&  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
.

Definition OS_QInit_partial_solve_wit_2 := OS_QInit_partial_solve_wit_2_pure -> OS_QInit_partial_solve_wit_2_aux.

Definition OS_QInit_partial_solve_wit_3_pure := 
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_post (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (((g_OSQTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (0 <= (g_OSQTbl (sg))) ” 
  &&  “ (((g_OSQTbl (sg)) + 96 ) <= 4294967296) ”
.

Definition OS_QInit_partial_solve_wit_3_aux := 
forall (sg: StableGlobVars) (PreH1 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH2 : (0 <= (g_OSQTbl (sg)))) (PreH3 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (queue_first_round_profile sg )) (PreH6 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH7 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH8 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH9 : (q_init_zynq7_reference_layout sg )) ,
  (mem_clr_post (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
|--
  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (((g_OSQTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (0 <= (g_OSQTbl (sg))) ” 
  &&  “ (((g_OSQTbl (sg)) + 96 ) <= 4294967296) ” 
  &&  “ (((g_OSQTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (0 <= (g_OSQTbl (sg))) ” 
  &&  “ (((g_OSQTbl (sg)) + 96 ) <= 4294967296) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (q_init_zynq7_reference_layout sg ) ”
  &&  (mem_clr_post (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
.

Definition OS_QInit_partial_solve_wit_3 := OS_QInit_partial_solve_wit_3_pure -> OS_QInit_partial_solve_wit_3_aux.

Definition OS_QInit_partial_solve_wit_4_pure := 
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" )))) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ”
) \/
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ”
).

Definition OS_QInit_partial_solve_wit_4_pure_split_goal_1 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ”
.

Definition OS_QInit_partial_solve_wit_4_pure_split_goal_2 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ”
.

Definition OS_QInit_partial_solve_wit_4_pure_split_goal_3 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ”
.

Definition OS_QInit_partial_solve_wit_4_pure_split_goal_4 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ”
.

Definition OS_QInit_partial_solve_wit_4_pure_split_goal_5 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ”
.

Definition OS_QInit_partial_solve_wit_4_pure_split_goal_6 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ”
.

Definition OS_QInit_partial_solve_wit_4_aux := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) < (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |-> (unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))))
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" )))) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) = (ix + 1 )) ” 
  &&  “ ((( &( "OSQTbl" ) ) + ((unsigned_last_nbits (((unsigned_last_nbits (ix) (32)) + 1 )) (16)) * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" )))) ” 
  &&  “ ((unsigned_last_nbits (ix) (32)) < (4 - 1 )) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ”
  &&  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pq2" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + ((ix + 1 ) * sizeof( "os_q" ))))
  **  (q_init_loop_state sg ix )
.

Definition OS_QInit_partial_solve_wit_4 := OS_QInit_partial_solve_wit_4_pure -> OS_QInit_partial_solve_wit_4_aux.

Definition OS_QInit_partial_solve_wit_5_pure := 
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |->_)
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix >= 3) ”
) \/
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |->_)
|--
  “ (ix >= 3) ”
).

Definition OS_QInit_partial_solve_wit_5_pure_split_goal_1 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (q_init_loop_state sg ix )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))
  **  ((( &( "pq2" ) )) # Ptr  |->_)
|--
  “ (ix >= 3) ”
.

Definition OS_QInit_partial_solve_wit_5_aux := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : ((unsigned_last_nbits (ix) (32)) >= (4 - 1 ))) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (queue_first_round_profile sg )) (PreH4 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH5 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH6 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) ,
  (q_init_loop_state sg ix )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix >= 3) ” 
  &&  “ ((unsigned_last_nbits (ix) (32)) >= (4 - 1 )) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ”
  &&  (q_init_loop_state sg ix )
.

Definition OS_QInit_partial_solve_wit_5 := OS_QInit_partial_solve_wit_5_pure -> OS_QInit_partial_solve_wit_5_aux.

Definition OS_QInit_partial_solve_wit_6_pure := 
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pq1" ) )) # Ptr  |-> pq1)
  **  (q_init_before_publish sg )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pq2" ) )) # Ptr  |->_)
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (3 = 3) ” 
  &&  “ ((( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" )))) ”
.

Definition OS_QInit_partial_solve_wit_6_aux := 
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pq1" ) )) # Ptr  |-> pq1)
  **  (q_init_before_publish sg )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (3 = 3) ” 
  &&  “ ((( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))) = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" )))) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix = 3) ” 
  &&  “ (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" )))) ”
  &&  ((( &( "ix" ) )) # UShort  |-> 3)
  **  ((( &( "pq1" ) )) # Ptr  |-> (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))
  **  (q_init_before_publish sg )
.

Definition OS_QInit_partial_solve_wit_6 := OS_QInit_partial_solve_wit_6_pure -> OS_QInit_partial_solve_wit_6_aux.

Definition OS_QInit_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (PreH1 : (queue_first_round_profile sg )) (PreH2 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) ,
  (queue_init_pre sg )
|--
  “ (((g_OSQTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (0 <= (g_OSQTbl (sg))) ” 
  &&  “ (((g_OSQTbl (sg)) + 96 ) <= 4294967296) ”
  &&  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
) \/
(
forall (sg: StableGlobVars) (PreH1 : (queue_first_round_profile sg )) (PreH2 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) ,
  (queue_init_pre sg )
|--
  EX (x: Z) ,
  “ (((g_OSQTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (0 <= (g_OSQTbl (sg))) ” 
  &&  “ (((g_OSQTbl (sg)) + 96 ) <= 4294967296) ”
  &&  (((g_OSQFreeList (sg))) # Ptr  |-> x)
  **  (mem_clr_pre (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
).

Definition OS_QInit_which_implies_wit_2 := 
(
forall (sg: StableGlobVars) (PreH1 : (queue_first_round_profile sg )) (PreH2 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH3 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH4 : (0 <= (g_OSQTbl (sg)))) (PreH5 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) ,
  (mem_clr_post (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
|--
  (q_init_after_clear sg )
) \/
(
forall (sg: StableGlobVars) (PreH1 : (queue_first_round_profile sg )) (PreH2 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH3 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH4 : (0 <= (g_OSQTbl (sg)))) (PreH5 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) ,
  (mem_clr_post (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
|--
  (q_init_after_clear sg )
).

Definition OS_QInit_which_implies_wit_2_split_goal_spatial := 
forall (sg: StableGlobVars) (PreH1 : (queue_first_round_profile sg )) (PreH2 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH3 : (((g_OSQTbl (sg)) % ( 4 ) ) = 0)) (PreH4 : (0 <= (g_OSQTbl (sg)))) (PreH5 : (((g_OSQTbl (sg)) + 96 ) <= 4294967296)) ,
  (mem_clr_post (( &( "OSQTbl" ) ) + (0 * sizeof( "os_q" ))) (sizeof( "os_q" ) * 4) )
  **  (((g_OSQFreeList (sg))) # Ptr  |->_)
|--
  (q_init_after_clear sg )
.

Definition OS_QInit_which_implies_wit_3 := 
(
forall (sg: StableGlobVars) (ix_next: Z) (ix: Z) (pq1: Z) (pq2: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix_next = (ix + 1 ))) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))) (PreH8 : (pq2 = (( &( "OSQTbl" ) ) + (ix_next * sizeof( "os_q" ))))) ,
  (q_init_loop_state sg ix )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix_next = (ix + 1 )) ” 
  &&  “ (pq1 = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" )))) ” 
  &&  “ (pq2 = (( &( "OSQTbl" ) ) + (ix_next * sizeof( "os_q" )))) ” 
  &&  “ (queue_control_block_layout_prop sg ix &((pq1)  # "os_q" ->ₛ "OSQPtr") &((pq1)  # "os_q" ->ₛ "OSQStart") &((pq1)  # "os_q" ->ₛ "OSQEnd") &((pq1)  # "os_q" ->ₛ "OSQIn") &((pq1)  # "os_q" ->ₛ "OSQOut") &((pq1)  # "os_q" ->ₛ "OSQSize") &((pq1)  # "os_q" ->ₛ "OSQEntries") ) ”
  &&  ((&((pq1)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_loop_residual sg ix )
) \/
(
forall (sg: StableGlobVars) (ix_next: Z) (ix: Z) (pq1: Z) (pq2: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix_next = (ix + 1 ))) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))) (PreH8 : (pq2 = (( &( "OSQTbl" ) ) + (ix_next * sizeof( "os_q" ))))) ,
  (q_init_loop_state sg ix )
|--
  “ (queue_control_block_layout_prop sg ix &((pq1)  # "os_q" ->ₛ "OSQPtr") &((pq1)  # "os_q" ->ₛ "OSQStart") &((pq1)  # "os_q" ->ₛ "OSQEnd") &((pq1)  # "os_q" ->ₛ "OSQIn") &((pq1)  # "os_q" ->ₛ "OSQOut") &((pq1)  # "os_q" ->ₛ "OSQSize") &((pq1)  # "os_q" ->ₛ "OSQEntries") ) ”
  &&  ((&((pq1)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_loop_residual sg ix )
).

Definition OS_QInit_which_implies_wit_3_split_goal_1 := 
forall (sg: StableGlobVars) (ix_next: Z) (ix: Z) (pq1: Z) (pq2: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix_next = (ix + 1 ))) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))) (PreH8 : (pq2 = (( &( "OSQTbl" ) ) + (ix_next * sizeof( "os_q" ))))) ,
  (q_init_loop_state sg ix )
|--
  “ (queue_control_block_layout_prop sg ix &((pq1)  # "os_q" ->ₛ "OSQPtr") &((pq1)  # "os_q" ->ₛ "OSQStart") &((pq1)  # "os_q" ->ₛ "OSQEnd") &((pq1)  # "os_q" ->ₛ "OSQIn") &((pq1)  # "os_q" ->ₛ "OSQOut") &((pq1)  # "os_q" ->ₛ "OSQSize") &((pq1)  # "os_q" ->ₛ "OSQEntries") ) ”
.

Definition OS_QInit_which_implies_wit_3_split_goal_spatial := 
forall (sg: StableGlobVars) (ix_next: Z) (ix: Z) (pq1: Z) (pq2: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix_next = (ix + 1 ))) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))) (PreH8 : (pq2 = (( &( "OSQTbl" ) ) + (ix_next * sizeof( "os_q" ))))) ,
  (q_init_loop_state sg ix )
|--
  ((&((pq1)  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_loop_residual sg ix )
.

Definition OS_QInit_which_implies_wit_4 := 
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix >= 3)) ,
  (q_init_loop_state sg ix )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix = 3) ” 
  &&  “ (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") ) ”
  &&  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_last_link_residual sg )
) \/
(
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix >= 3)) ,
  (q_init_loop_state sg ix )
|--
  “ (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") ) ” 
  &&  “ (ix = 3) ”
  &&  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_last_link_residual sg )
).

Definition OS_QInit_which_implies_wit_4_split_goal_1 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix >= 3)) ,
  (q_init_loop_state sg ix )
|--
  “ (queue_control_block_layout_prop sg ix &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQStart") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEnd") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQIn") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQOut") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQSize") &(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQEntries") ) ”
.

Definition OS_QInit_which_implies_wit_4_split_goal_2 := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix >= 3)) ,
  (q_init_loop_state sg ix )
|--
  “ (ix = 3) ”
.

Definition OS_QInit_which_implies_wit_4_split_goal_spatial := 
forall (sg: StableGlobVars) (ix: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix >= 3)) ,
  (q_init_loop_state sg ix )
|--
  ((&(((( &( "OSQTbl" ) ) + (ix * sizeof( "os_q" ))))  # "os_q" ->ₛ "OSQPtr")) # Ptr  |-> 0)
  **  (q_init_last_link_residual sg )
.

Definition OS_QInit_which_implies_wit_5 := 
(
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  (q_init_before_publish sg )
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix = 3) ” 
  &&  “ (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" )))) ”
  &&  ((( &( "OSQFreeList" ) )) # Ptr  |->_)
  **  (q_init_publish_residual sg )
) \/
(
forall (sg: StableGlobVars) (ix: Z) (pq1: Z) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (queue_first_round_profile sg )) (PreH3 : (os_q_table_addr sg ( &( "OSQTbl" ) ) )) (PreH4 : (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) )) (PreH5 : (queue_table_layout_prop sg ( &( "OSQTbl" ) ) )) (PreH6 : (ix = 3)) (PreH7 : (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" ))))) ,
  (q_init_before_publish sg )
|--
  EX (x: Z) ,
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (queue_first_round_profile sg ) ” 
  &&  “ (os_q_table_addr sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (os_q_free_list_addr sg ( &( "OSQFreeList" ) ) ) ” 
  &&  “ (queue_table_layout_prop sg ( &( "OSQTbl" ) ) ) ” 
  &&  “ (ix = 3) ” 
  &&  “ (pq1 = (( &( "OSQTbl" ) ) + (3 * sizeof( "os_q" )))) ”
  &&  ((( &( "OSQFreeList" ) )) # Ptr  |-> x)
  **  (q_init_publish_residual sg )
).

Module Type VC_Correct.


Axiom proof_of_OS_QInit_safety_wit_1 : OS_QInit_safety_wit_1.
Axiom proof_of_OS_QInit_safety_wit_2 : OS_QInit_safety_wit_2.
Axiom proof_of_OS_QInit_safety_wit_3 : OS_QInit_safety_wit_3.
Axiom proof_of_OS_QInit_entail_wit_1 : OS_QInit_entail_wit_1.
Axiom proof_of_OS_QInit_entail_wit_2 : OS_QInit_entail_wit_2.
Axiom proof_of_OS_QInit_entail_wit_3 : OS_QInit_entail_wit_3.
Axiom proof_of_OS_QInit_entail_wit_4 : OS_QInit_entail_wit_4.
Axiom proof_of_OS_QInit_return_wit_1 : OS_QInit_return_wit_1.
Axiom proof_of_OS_QInit_partial_solve_wit_1_pure : OS_QInit_partial_solve_wit_1_pure.
Axiom proof_of_OS_QInit_partial_solve_wit_1 : OS_QInit_partial_solve_wit_1.
Axiom proof_of_OS_QInit_partial_solve_wit_2_pure : OS_QInit_partial_solve_wit_2_pure.
Axiom proof_of_OS_QInit_partial_solve_wit_2 : OS_QInit_partial_solve_wit_2.
Axiom proof_of_OS_QInit_partial_solve_wit_3_pure : OS_QInit_partial_solve_wit_3_pure.
Axiom proof_of_OS_QInit_partial_solve_wit_3 : OS_QInit_partial_solve_wit_3.
Axiom proof_of_OS_QInit_partial_solve_wit_4_pure : OS_QInit_partial_solve_wit_4_pure.
Axiom proof_of_OS_QInit_partial_solve_wit_4 : OS_QInit_partial_solve_wit_4.
Axiom proof_of_OS_QInit_partial_solve_wit_5_pure : OS_QInit_partial_solve_wit_5_pure.
Axiom proof_of_OS_QInit_partial_solve_wit_5 : OS_QInit_partial_solve_wit_5.
Axiom proof_of_OS_QInit_partial_solve_wit_6_pure : OS_QInit_partial_solve_wit_6_pure.
Axiom proof_of_OS_QInit_partial_solve_wit_6 : OS_QInit_partial_solve_wit_6.
Axiom proof_of_OS_QInit_which_implies_wit_1 : OS_QInit_which_implies_wit_1.
Axiom proof_of_OS_QInit_which_implies_wit_2 : OS_QInit_which_implies_wit_2.
Axiom proof_of_OS_QInit_which_implies_wit_3 : OS_QInit_which_implies_wit_3.
Axiom proof_of_OS_QInit_which_implies_wit_4 : OS_QInit_which_implies_wit_4.
Axiom proof_of_OS_QInit_which_implies_wit_5 : OS_QInit_which_implies_wit_5.

End VC_Correct.
