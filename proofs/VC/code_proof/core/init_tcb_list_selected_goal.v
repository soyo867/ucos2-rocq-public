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
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_tcb_list_selected_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_InitTCBList -----*)

Definition OS_InitTCBList_safety_wit_1 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_2 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_3 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) (PreH6 : ((ix + 1 ) = (ix + 1 ))) (PreH7 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH8 : ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))) (PreH9 : (ix < ((20 + 2 ) - 1 ))) (PreH10 : (init_tcb_list_profile sg )) (PreH11 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH12 : (init_tcb_list_layout sg )) (PreH13 : (0 <= ix)) (PreH14 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ix_next" ) )) # UChar  |-> (ix + 1 ))
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_4 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (ix = 21)) (PreH5 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH6 : (ix >= ((20 + 2 ) - 1 ))) (PreH7 : (init_tcb_list_profile sg )) (PreH8 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH9 : (init_tcb_list_layout sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 21)) ,
  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_5 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (ix = 21)) (PreH5 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH6 : (ix >= ((20 + 2 ) - 1 ))) (PreH7 : (init_tcb_list_profile sg )) (PreH8 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH9 : (init_tcb_list_layout sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_6 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (init_tcb_list_profile sg )) (PreH5 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_7 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (init_tcb_list_profile sg )) (PreH5 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_entail_wit_1 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (init_tcb_list_profile sg )) (PreH5 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout sg )) (PreH7 : (sizeof( "os_tcb" ) = 64)) (PreH8 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH9 : ((sizeof(PTR) * 64) = 256)) (PreH10 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH11 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH13 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : (init_tcb_list_profile sg )) (PreH15 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH16 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 21) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_entail_wit_2 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) (PreH6 : ((ix + 1 ) = (ix + 1 ))) (PreH7 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH8 : ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))) (PreH9 : (ix < ((20 + 2 ) - 1 ))) (PreH10 : (init_tcb_list_profile sg )) (PreH11 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH12 : (init_tcb_list_layout sg )) (PreH13 : (0 <= ix)) (PreH14 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix_next" ) )) # UChar  |-> (ix + 1 ))
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) (PreH6 : (ix < ((20 + 2 ) - 1 ))) (PreH7 : (init_tcb_list_profile sg )) (PreH8 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH9 : (init_tcb_list_layout sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
).

Definition OS_InitTCBList_entail_wit_2_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) (PreH6 : (ix < ((20 + 2 ) - 1 ))) (PreH7 : (init_tcb_list_profile sg )) (PreH8 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH9 : (init_tcb_list_layout sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_entail_wit_3 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= (ix + 1 )) ” 
  &&  “ ((ix + 1 ) <= 21) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_entail_wit_4 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (ix = 21)) (PreH5 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH6 : (ix >= ((20 + 2 ) - 1 ))) (PreH7 : (init_tcb_list_profile sg )) (PreH8 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH9 : (init_tcb_list_layout sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (ix = 21)) (PreH5 : (ix >= ((20 + 2 ) - 1 ))) (PreH6 : (init_tcb_list_profile sg )) (PreH7 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH8 : (init_tcb_list_layout sg )) (PreH9 : (0 <= ix)) (PreH10 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
).

Definition OS_InitTCBList_entail_wit_4_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (ix = 21)) (PreH5 : (ix >= ((20 + 2 ) - 1 ))) (PreH6 : (init_tcb_list_profile sg )) (PreH7 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH8 : (init_tcb_list_layout sg )) (PreH9 : (0 <= ix)) (PreH10 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_return_wit_1 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (init_tcb_list_profile sg )) (PreH5 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (init_tcb_list_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (init_tcb_list_profile sg )) (PreH5 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))
  **  (GlobalStrings LitMap )
|--
  (init_tcb_list_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
).

Definition OS_InitTCBList_return_wit_1_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (init_tcb_list_profile sg )) (PreH5 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH6 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))
  **  (GlobalStrings LitMap )
|--
  (init_tcb_list_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_1_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (init_tcb_list_pre sg )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
.

Definition OS_InitTCBList_partial_solve_wit_1_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (init_tcb_list_pre sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_1 := OS_InitTCBList_partial_solve_wit_1_pure -> OS_InitTCBList_partial_solve_wit_1_aux.

Definition OS_InitTCBList_partial_solve_wit_2_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= (sizeof( "os_tcb" ) * 22)) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_InitTCBList_partial_solve_wit_2_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= (sizeof( "os_tcb" ) * 22)) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 1408) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_2 := OS_InitTCBList_partial_solve_wit_2_pure -> OS_InitTCBList_partial_solve_wit_2_aux.

Definition OS_InitTCBList_partial_solve_wit_3_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (0 <= (sizeof(PTR) * 64)) ” 
  &&  “ ((sizeof(PTR) * 64) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_InitTCBList_partial_solve_wit_3_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= (sizeof(PTR) * 64)) ” 
  &&  “ ((sizeof(PTR) * 64) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 1408) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (init_tcb_list_roots sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_3 := OS_InitTCBList_partial_solve_wit_3_pure -> OS_InitTCBList_partial_solve_wit_3_aux.

Definition OS_InitTCBList_partial_solve_wit_4_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (init_tcb_list_roots sg )
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
.

Definition OS_InitTCBList_partial_solve_wit_4_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (sizeof( "os_tcb" ) = 64)) (PreH5 : ((sizeof( "os_tcb" ) * 22) = 1408)) (PreH6 : ((sizeof(PTR) * 64) = 256)) (PreH7 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH8 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH10 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (init_tcb_list_profile sg )) (PreH12 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (init_tcb_list_roots sg )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 1408) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_4 := OS_InitTCBList_partial_solve_wit_4_pure -> OS_InitTCBList_partial_solve_wit_4_aux.

Definition OS_InitTCBList_partial_solve_wit_5_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_profile sg )) (PreH3 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 21)) ,
  ((( &( "ix" ) )) # UChar  |-> ix)
  **  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |-> (ix + 1 ))
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" )))) ”
.

Definition OS_InitTCBList_partial_solve_wit_5_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_profile sg )) (PreH3 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 21)) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" )))) ” 
  &&  “ (ix < ((20 + 2 ) - 1 )) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 21) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_5 := OS_InitTCBList_partial_solve_wit_5_pure -> OS_InitTCBList_partial_solve_wit_5_aux.

Definition OS_InitTCBList_partial_solve_wit_6_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_profile sg )) (PreH3 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 21)) ,
  ((( &( "ix" ) )) # UChar  |-> ix)
  **  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (21 <= ix) ” 
  &&  “ (ix <= 21) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ”
.

Definition OS_InitTCBList_partial_solve_wit_6_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_profile sg )) (PreH3 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 21)) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (21 <= ix) ” 
  &&  “ (ix <= 21) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ (ix >= ((20 + 2 ) - 1 )) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 21) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_6 := OS_InitTCBList_partial_solve_wit_6_pure -> OS_InitTCBList_partial_solve_wit_6_aux.

Definition OS_InitTCBList_partial_solve_wit_7_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
.

Definition OS_InitTCBList_partial_solve_wit_7_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_7 := OS_InitTCBList_partial_solve_wit_7_pure -> OS_InitTCBList_partial_solve_wit_7_aux.

Definition OS_InitTCBList_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 64) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 1408) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
) \/
(
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
|--
  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ”
  &&  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
).

Definition OS_InitTCBList_which_implies_wit_1_split_goal_1 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
|--
  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_2 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
|--
  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_3 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
|--
  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_4 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
|--
  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_spatial := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_pre sg )
|--
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
.

Definition OS_InitTCBList_which_implies_wit_2 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 0 )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
|--
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 0 )
).

Definition OS_InitTCBList_which_implies_wit_2_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_roots sg )
|--
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 0 )
.

Definition OS_InitTCBList_which_implies_wit_3 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (ptcb1: Z) (ptcb2: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) (PreH6 : (ix_next = (ix + 1 ))) (PreH7 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH8 : (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ” 
  &&  “ (ix_next = (ix + 1 )) ” 
  &&  “ (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" )))) ”
  &&  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (ptcb1: Z) (ptcb2: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) (PreH6 : (ix_next = (ix + 1 ))) (PreH7 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH8 : (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
).

Definition OS_InitTCBList_which_implies_wit_3_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (ptcb1: Z) (ptcb2: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (0 <= ix)) (PreH5 : (ix < 21)) (PreH6 : (ix_next = (ix + 1 ))) (PreH7 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH8 : (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
.

Definition OS_InitTCBList_which_implies_wit_4 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ptcb1: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (21 <= ix)) (PreH5 : (ix <= 21)) (PreH6 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ” 
  &&  “ (ix = 21) ” 
  &&  “ (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ”
  &&  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ptcb1: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (21 <= ix)) (PreH5 : (ix <= 21)) (PreH6 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
).

Definition OS_InitTCBList_which_implies_wit_4_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ptcb1: Z) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) (PreH4 : (21 <= ix)) (PreH5 : (ix <= 21)) (PreH6 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_loop_residual sg (LitMap (("?"%string))) ix )
.

Definition OS_InitTCBList_which_implies_wit_5 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
|--
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  (init_tcb_list_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_profile sg )) (PreH2 : (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_layout sg )) ,
  (init_tcb_list_loop_state sg (LitMap (("?"%string))) 22 )
|--
  EX (x_2: Z)  (x: Z) ,
  “ (init_tcb_list_profile sg ) ” 
  &&  “ (init_tcb_list_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_layout sg ) ”
  &&  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> x_2)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> x)
  **  (init_tcb_list_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_priority_zero sg )
).

Module Type VC_Correct.


Axiom proof_of_OS_InitTCBList_safety_wit_1 : OS_InitTCBList_safety_wit_1.
Axiom proof_of_OS_InitTCBList_safety_wit_2 : OS_InitTCBList_safety_wit_2.
Axiom proof_of_OS_InitTCBList_safety_wit_3 : OS_InitTCBList_safety_wit_3.
Axiom proof_of_OS_InitTCBList_safety_wit_4 : OS_InitTCBList_safety_wit_4.
Axiom proof_of_OS_InitTCBList_safety_wit_5 : OS_InitTCBList_safety_wit_5.
Axiom proof_of_OS_InitTCBList_safety_wit_6 : OS_InitTCBList_safety_wit_6.
Axiom proof_of_OS_InitTCBList_safety_wit_7 : OS_InitTCBList_safety_wit_7.
Axiom proof_of_OS_InitTCBList_entail_wit_1 : OS_InitTCBList_entail_wit_1.
Axiom proof_of_OS_InitTCBList_entail_wit_2 : OS_InitTCBList_entail_wit_2.
Axiom proof_of_OS_InitTCBList_entail_wit_3 : OS_InitTCBList_entail_wit_3.
Axiom proof_of_OS_InitTCBList_entail_wit_4 : OS_InitTCBList_entail_wit_4.
Axiom proof_of_OS_InitTCBList_return_wit_1 : OS_InitTCBList_return_wit_1.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_1_pure : OS_InitTCBList_partial_solve_wit_1_pure.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_1 : OS_InitTCBList_partial_solve_wit_1.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_2_pure : OS_InitTCBList_partial_solve_wit_2_pure.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_2 : OS_InitTCBList_partial_solve_wit_2.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_3_pure : OS_InitTCBList_partial_solve_wit_3_pure.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_3 : OS_InitTCBList_partial_solve_wit_3.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_4_pure : OS_InitTCBList_partial_solve_wit_4_pure.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_4 : OS_InitTCBList_partial_solve_wit_4.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_5_pure : OS_InitTCBList_partial_solve_wit_5_pure.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_5 : OS_InitTCBList_partial_solve_wit_5.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_6_pure : OS_InitTCBList_partial_solve_wit_6_pure.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_6 : OS_InitTCBList_partial_solve_wit_6.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_7_pure : OS_InitTCBList_partial_solve_wit_7_pure.
Axiom proof_of_OS_InitTCBList_partial_solve_wit_7 : OS_InitTCBList_partial_solve_wit_7.
Axiom proof_of_OS_InitTCBList_which_implies_wit_1 : OS_InitTCBList_which_implies_wit_1.
Axiom proof_of_OS_InitTCBList_which_implies_wit_2 : OS_InitTCBList_which_implies_wit_2.
Axiom proof_of_OS_InitTCBList_which_implies_wit_3 : OS_InitTCBList_which_implies_wit_3.
Axiom proof_of_OS_InitTCBList_which_implies_wit_4 : OS_InitTCBList_which_implies_wit_4.
Axiom proof_of_OS_InitTCBList_which_implies_wit_5 : OS_InitTCBList_which_implies_wit_5.

End VC_Correct.
