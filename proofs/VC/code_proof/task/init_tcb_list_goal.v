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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_prio_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_InitTCBList -----*)

Definition OS_InitTCBList_safety_wit_1 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
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
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
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
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) (PreH7 : ((ix + 1 ) = (ix + 1 ))) (PreH8 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH9 : ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))) (PreH10 : (ix < ((20 + 2 ) - 1 ))) (PreH11 : (init_tcb_list_full_profile sg )) (PreH12 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_full_layout sg )) (PreH14 : (init_tcb_list_full_field_layout sg )) (PreH15 : (0 <= ix)) (PreH16 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ix_next" ) )) # UChar  |-> (ix + 1 ))
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_4 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (ix = 21)) (PreH6 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH7 : (ix >= ((20 + 2 ) - 1 ))) (PreH8 : (init_tcb_list_full_profile sg )) (PreH9 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH10 : (init_tcb_list_full_layout sg )) (PreH11 : (init_tcb_list_full_field_layout sg )) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 21)) ,
  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_5 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (ix = 21)) (PreH6 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH7 : (ix >= ((20 + 2 ) - 1 ))) (PreH8 : (init_tcb_list_full_profile sg )) (PreH9 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH10 : (init_tcb_list_full_layout sg )) (PreH11 : (init_tcb_list_full_field_layout sg )) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitTCBList_safety_wit_6 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (init_tcb_list_full_profile sg )) (PreH6 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH7 : (init_tcb_list_full_layout sg )) (PreH8 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_full_priority_zero sg )
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
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (init_tcb_list_full_profile sg )) (PreH6 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH7 : (init_tcb_list_full_layout sg )) (PreH8 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_full_priority_zero sg )
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
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (init_tcb_list_full_profile sg )) (PreH6 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH7 : (init_tcb_list_full_layout sg )) (PreH8 : (init_tcb_list_full_field_layout sg )) (PreH9 : (sizeof( "os_tcb" ) = 92)) (PreH10 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH11 : ((sizeof(PTR) * 64) = 256)) (PreH12 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH13 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH14 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH15 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH16 : (init_tcb_list_full_profile sg )) (PreH17 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH18 : (init_tcb_list_full_layout sg )) (PreH19 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 21) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_entail_wit_2 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) (PreH7 : ((ix + 1 ) = (ix + 1 ))) (PreH8 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH9 : ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))) (PreH10 : (ix < ((20 + 2 ) - 1 ))) (PreH11 : (init_tcb_list_full_profile sg )) (PreH12 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH13 : (init_tcb_list_full_layout sg )) (PreH14 : (init_tcb_list_full_field_layout sg )) (PreH15 : (0 <= ix)) (PreH16 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix_next" ) )) # UChar  |-> (ix + 1 ))
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) (PreH7 : (ix < ((20 + 2 ) - 1 ))) (PreH8 : (init_tcb_list_full_profile sg )) (PreH9 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH10 : (init_tcb_list_full_layout sg )) (PreH11 : (init_tcb_list_full_field_layout sg )) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
).

Definition OS_InitTCBList_entail_wit_2_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) (PreH7 : (ix < ((20 + 2 ) - 1 ))) (PreH8 : (init_tcb_list_full_profile sg )) (PreH9 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH10 : (init_tcb_list_full_layout sg )) (PreH11 : (init_tcb_list_full_field_layout sg )) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_entail_wit_3 := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= (ix + 1 )) ” 
  &&  “ ((ix + 1 ) <= 21) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_entail_wit_4 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (ix = 21)) (PreH6 : ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH7 : (ix >= ((20 + 2 ) - 1 ))) (PreH8 : (init_tcb_list_full_profile sg )) (PreH9 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH10 : (init_tcb_list_full_layout sg )) (PreH11 : (init_tcb_list_full_field_layout sg )) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 21)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UChar  |-> ix)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (ix = 21)) (PreH6 : (ix >= ((20 + 2 ) - 1 ))) (PreH7 : (init_tcb_list_full_profile sg )) (PreH8 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH9 : (init_tcb_list_full_layout sg )) (PreH10 : (init_tcb_list_full_field_layout sg )) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
).

Definition OS_InitTCBList_entail_wit_4_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (ix = 21)) (PreH6 : (ix >= ((20 + 2 ) - 1 ))) (PreH7 : (init_tcb_list_full_profile sg )) (PreH8 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH9 : (init_tcb_list_full_layout sg )) (PreH10 : (init_tcb_list_full_field_layout sg )) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 21)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
|--
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_return_wit_1 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (init_tcb_list_full_profile sg )) (PreH6 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH7 : (init_tcb_list_full_layout sg )) (PreH8 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_full_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (init_tcb_list_full_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (init_tcb_list_full_profile sg )) (PreH6 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH7 : (init_tcb_list_full_layout sg )) (PreH8 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_full_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))
  **  (GlobalStrings LitMap )
|--
  (init_tcb_list_full_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
).

Definition OS_InitTCBList_return_wit_1_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (init_tcb_list_full_profile sg )) (PreH6 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH7 : (init_tcb_list_full_layout sg )) (PreH8 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_full_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))
  **  (GlobalStrings LitMap )
|--
  (init_tcb_list_full_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_1_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (init_tcb_list_full_pre sg )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
.

Definition OS_InitTCBList_partial_solve_wit_1_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (init_tcb_list_full_pre sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_1 := OS_InitTCBList_partial_solve_wit_1_pure -> OS_InitTCBList_partial_solve_wit_1_aux.

Definition OS_InitTCBList_partial_solve_wit_2_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
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
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= (sizeof( "os_tcb" ) * 22)) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 92) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 2024) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_2 := OS_InitTCBList_partial_solve_wit_2_pure -> OS_InitTCBList_partial_solve_wit_2_aux.

Definition OS_InitTCBList_partial_solve_wit_3_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
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
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= (sizeof(PTR) * 64)) ” 
  &&  “ ((sizeof(PTR) * 64) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 92) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 2024) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (init_tcb_list_full_roots sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_3 := OS_InitTCBList_partial_solve_wit_3_pure -> OS_InitTCBList_partial_solve_wit_3_aux.

Definition OS_InitTCBList_partial_solve_wit_4_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (init_tcb_list_full_roots sg )
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
.

Definition OS_InitTCBList_partial_solve_wit_4_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (sizeof( "os_tcb" ) = 92)) (PreH6 : ((sizeof( "os_tcb" ) * 22) = 2024)) (PreH7 : ((sizeof(PTR) * 64) = 256)) (PreH8 : (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))))) (PreH9 : (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))))) (PreH11 : (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (init_tcb_list_full_profile sg )) (PreH13 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH14 : (init_tcb_list_full_layout sg )) (PreH15 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (init_tcb_list_full_roots sg )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 92) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 2024) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_4 := OS_InitTCBList_partial_solve_wit_4_pure -> OS_InitTCBList_partial_solve_wit_4_aux.

Definition OS_InitTCBList_partial_solve_wit_5_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_full_profile sg )) (PreH3 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_full_layout sg )) (PreH5 : (init_tcb_list_full_field_layout sg )) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 21)) ,
  ((( &( "ix" ) )) # UChar  |-> ix)
  **  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |-> (ix + 1 ))
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))))
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" )))) ”
.

Definition OS_InitTCBList_partial_solve_wit_5_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_full_profile sg )) (PreH3 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_full_layout sg )) (PreH5 : (init_tcb_list_full_field_layout sg )) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 21)) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + ((ix + 1 ) * sizeof( "os_tcb" )))) ” 
  &&  “ (ix < ((20 + 2 ) - 1 )) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 21) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_5 := OS_InitTCBList_partial_solve_wit_5_pure -> OS_InitTCBList_partial_solve_wit_5_aux.

Definition OS_InitTCBList_partial_solve_wit_6_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_full_profile sg )) (PreH3 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_full_layout sg )) (PreH5 : (init_tcb_list_full_field_layout sg )) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 21)) ,
  ((( &( "ix" ) )) # UChar  |-> ix)
  **  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |-> (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (21 <= ix) ” 
  &&  “ (ix <= 21) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ”
.

Definition OS_InitTCBList_partial_solve_wit_6_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= ((20 + 2 ) - 1 ))) (PreH2 : (init_tcb_list_full_profile sg )) (PreH3 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH4 : (init_tcb_list_full_layout sg )) (PreH5 : (init_tcb_list_full_field_layout sg )) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 21)) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (21 <= ix) ” 
  &&  “ (ix <= 21) ” 
  &&  “ ((( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))) = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ (ix >= ((20 + 2 ) - 1 )) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 21) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_6 := OS_InitTCBList_partial_solve_wit_6_pure -> OS_InitTCBList_partial_solve_wit_6_aux.

Definition OS_InitTCBList_partial_solve_wit_7_pure := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
  **  ((( &( "ix" ) )) # UChar  |->_)
  **  ((( &( "ix_next" ) )) # UChar  |->_)
  **  ((( &( "ptcb1" ) )) # Ptr  |->_)
  **  ((( &( "ptcb2" ) )) # Ptr  |->_)
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
.

Definition OS_InitTCBList_partial_solve_wit_7_aux := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
  **  (GlobalStrings LitMap )
.

Definition OS_InitTCBList_partial_solve_wit_7 := OS_InitTCBList_partial_solve_wit_7_pure -> OS_InitTCBList_partial_solve_wit_7_aux.

Definition OS_InitTCBList_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (sizeof( "os_tcb" ) = 92) ” 
  &&  “ ((sizeof( "os_tcb" ) * 22) = 2024) ” 
  &&  “ ((sizeof(PTR) * 64) = 256) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
) \/
(
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
|--
  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ” 
  &&  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ”
  &&  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
).

Definition OS_InitTCBList_which_implies_wit_1_split_goal_1 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
|--
  “ (((( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) + ((sizeof(PTR) * 64) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_2 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
|--
  “ (0 <= (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR)))) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_3 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
|--
  “ (((( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) + ((sizeof( "os_tcb" ) * 22) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_4 := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
|--
  “ (0 <= (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" )))) ”
.

Definition OS_InitTCBList_which_implies_wit_1_split_goal_spatial := 
forall (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_pre sg )
|--
  (mem_clr_pre (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_pre (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
.

Definition OS_InitTCBList_which_implies_wit_2 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 0 )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
|--
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 0 )
).

Definition OS_InitTCBList_which_implies_wit_2_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (mem_clr_post (( &( "OSTCBTbl" ) ) + (0 * sizeof( "os_tcb" ))) (sizeof( "os_tcb" ) * 22) )
  **  (mem_clr_post (( &( "OSTCBPrioTbl" ) ) + (0 * sizeof(PTR))) (sizeof(PTR) * 64) )
  **  (init_tcb_list_full_roots sg )
|--
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 0 )
.

Definition OS_InitTCBList_which_implies_wit_3 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (ptcb1: Z) (ptcb2: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) (PreH7 : (ix_next = (ix + 1 ))) (PreH8 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH9 : (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 21) ” 
  &&  “ (ix_next = (ix + 1 )) ” 
  &&  “ (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ” 
  &&  “ (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" )))) ”
  &&  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (ptcb1: Z) (ptcb2: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) (PreH7 : (ix_next = (ix + 1 ))) (PreH8 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH9 : (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
).

Definition OS_InitTCBList_which_implies_wit_3_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (ptcb1: Z) (ptcb2: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (0 <= ix)) (PreH6 : (ix < 21)) (PreH7 : (ix_next = (ix + 1 ))) (PreH8 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) (PreH9 : (ptcb2 = (( &( "OSTCBTbl" ) ) + (ix_next * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
.

Definition OS_InitTCBList_which_implies_wit_4 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ptcb1: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (21 <= ix)) (PreH6 : (ix <= 21)) (PreH7 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ” 
  &&  “ (ix = 21) ” 
  &&  “ (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" )))) ”
  &&  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ptcb1: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (21 <= ix)) (PreH6 : (ix <= 21)) (PreH7 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
).

Definition OS_InitTCBList_which_implies_wit_4_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ptcb1: Z) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) (PreH5 : (21 <= ix)) (PreH6 : (ix <= 21)) (PreH7 : (ptcb1 = (( &( "OSTCBTbl" ) ) + (ix * sizeof( "os_tcb" ))))) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBNext")) # Ptr  |-> 0)
  **  ((&((ptcb1)  # "os_tcb" ->ₛ "OSTCBTaskName")) # Ptr  |-> 0)
  **  (init_tcb_list_full_loop_residual sg (LitMap (("?"%string))) ix )
.

Definition OS_InitTCBList_which_implies_wit_5 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
|--
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  (init_tcb_list_full_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_full_priority_zero sg )
  **  ((( &( "OSTCBList" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBFreeList" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (init_tcb_list_full_profile sg )) (PreH2 : (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) )) (PreH3 : (init_tcb_list_full_layout sg )) (PreH4 : (init_tcb_list_full_field_layout sg )) ,
  (init_tcb_list_full_loop_state sg (LitMap (("?"%string))) 22 )
|--
  EX (x_2: Z)  (x: Z) ,
  “ (init_tcb_list_full_profile sg ) ” 
  &&  “ (init_tcb_list_full_global_addresses sg ( &( "OSTCBTbl" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBFreeList" ) ) ) ” 
  &&  “ (init_tcb_list_full_layout sg ) ” 
  &&  “ (init_tcb_list_full_field_layout sg ) ”
  &&  ((( &( "OSTCBFreeList" ) )) # Ptr  |-> x_2)
  **  ((( &( "OSTCBList" ) )) # Ptr  |-> x)
  **  (init_tcb_list_full_prefix sg (LitMap (("?"%string))) 22 )
  **  (init_tcb_list_full_priority_zero sg )
).

(*----- Function OS_MemClr -----*)

Definition OS_MemClr_safety_wit_1 := 
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : ((pdest_pre + ((size_pre - size ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH7 : (size > 0)) (PreH8 : (0 <= size)) (PreH9 : (size <= size_pre)) (PreH10 : (size_pre <= 65535)) (PreH11 : (0 <= pdest_pre)) (PreH12 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  ((( &( "size" ) )) # UShort  |-> size)
  **  ((( &( "pdest" ) )) # Ptr  |-> (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))
  **  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (mem_clr_loop_residual pdest_pre size_pre size )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_MemClr_entail_wit_1 := 
(
forall (size_pre: Z) (pdest_pre: Z) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre <= 65535)) (PreH3 : (0 <= pdest_pre)) (PreH4 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) ,
  (mem_clr_pre pdest_pre size_pre )
|--
  “ (0 <= size_pre) ” 
  &&  “ (size_pre <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest_pre = (pdest_pre + ((size_pre - size_pre ) * sizeof(UCHAR)))) ”
  &&  (mem_clr_loop_state pdest_pre size_pre size_pre )
) \/
(
forall (size_pre: Z) (pdest_pre: Z) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre <= 65535)) (PreH3 : (0 <= pdest_pre)) (PreH4 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) ,
  (mem_clr_pre pdest_pre size_pre )
|--
  (mem_clr_loop_state pdest_pre size_pre size_pre )
).

Definition OS_MemClr_entail_wit_1_split_goal_spatial := 
forall (size_pre: Z) (pdest_pre: Z) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre <= 65535)) (PreH3 : (0 <= pdest_pre)) (PreH4 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) ,
  (mem_clr_pre pdest_pre size_pre )
|--
  (mem_clr_loop_state pdest_pre size_pre size_pre )
.

Definition OS_MemClr_entail_wit_2 := 
(
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : ((pdest_pre + ((size_pre - size ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH7 : (size > 0)) (PreH8 : (0 <= size)) (PreH9 : (size <= size_pre)) (PreH10 : (size_pre <= 65535)) (PreH11 : (0 <= pdest_pre)) (PreH12 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH13 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (mem_clr_loop_residual pdest_pre size_pre size )
|--
  “ (0 <= (size - 1 )) ” 
  &&  “ ((size - 1 ) <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((pdest_pre + (((size_pre - size ) + 1 ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - (size - 1 ) ) * sizeof(UCHAR)))) ”
  &&  (mem_clr_loop_state pdest_pre size_pre (size - 1 ) )
) \/
(
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : (size > 0)) (PreH7 : (0 <= size)) (PreH8 : (size <= size_pre)) (PreH9 : (size_pre <= 65535)) (PreH10 : (0 <= pdest_pre)) (PreH11 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (mem_clr_loop_residual pdest_pre size_pre size )
|--
  (mem_clr_loop_state pdest_pre size_pre (size - 1 ) )
).

Definition OS_MemClr_entail_wit_2_split_goal_spatial := 
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : (size > 0)) (PreH7 : (0 <= size)) (PreH8 : (size <= size_pre)) (PreH9 : (size_pre <= 65535)) (PreH10 : (0 <= pdest_pre)) (PreH11 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH12 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (mem_clr_loop_residual pdest_pre size_pre size )
|--
  (mem_clr_loop_state pdest_pre size_pre (size - 1 ) )
.

Definition OS_MemClr_return_wit_1 := 
(
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (mem_clr_loop_state pdest_pre size_pre size )
|--
  (mem_clr_post pdest_pre size_pre )
) \/
(
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (mem_clr_loop_state pdest_pre size_pre size )
|--
  (mem_clr_post pdest_pre size_pre )
).

Definition OS_MemClr_return_wit_1_split_goal_spatial := 
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (mem_clr_loop_state pdest_pre size_pre size )
|--
  (mem_clr_post pdest_pre size_pre )
.

Definition OS_MemClr_partial_solve_wit_1_pure := 
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  ((( &( "size" ) )) # UShort  |-> size)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (mem_clr_loop_state pdest_pre size_pre size )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((pdest_pre + ((size_pre - size ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
.

Definition OS_MemClr_partial_solve_wit_1_aux := 
forall (size_pre: Z) (pdest_pre: Z) (pdest: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  (mem_clr_loop_state pdest_pre size_pre size )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((pdest_pre + ((size_pre - size ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ (size > 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
  &&  ((( &( "pdest" ) )) # Ptr  |-> (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))
  **  (mem_clr_loop_state pdest_pre size_pre size )
.

Definition OS_MemClr_partial_solve_wit_1 := OS_MemClr_partial_solve_wit_1_pure -> OS_MemClr_partial_solve_wit_1_aux.

Definition OS_MemClr_which_implies_wit_1 := 
(
forall (size_pre: Z) (pdest_pre: Z) (size: Z) (pdest: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (mem_clr_loop_state pdest_pre size_pre size )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
  &&  ((pdest) # UChar  |->_)
  **  (mem_clr_loop_residual pdest_pre size_pre size )
) \/
(
forall (size_pre: Z) (pdest_pre: Z) (size: Z) (pdest: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (mem_clr_loop_state pdest_pre size_pre size )
|--
  EX (x: Z) ,
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
  &&  ((pdest) # UChar  |-> x)
  **  (mem_clr_loop_residual pdest_pre size_pre size )
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
Axiom proof_of_OS_MemClr_safety_wit_1 : OS_MemClr_safety_wit_1.
Axiom proof_of_OS_MemClr_entail_wit_1 : OS_MemClr_entail_wit_1.
Axiom proof_of_OS_MemClr_entail_wit_2 : OS_MemClr_entail_wit_2.
Axiom proof_of_OS_MemClr_return_wit_1 : OS_MemClr_return_wit_1.
Axiom proof_of_OS_MemClr_partial_solve_wit_1_pure : OS_MemClr_partial_solve_wit_1_pure.
Axiom proof_of_OS_MemClr_partial_solve_wit_1 : OS_MemClr_partial_solve_wit_1.
Axiom proof_of_OS_MemClr_which_implies_wit_1 : OS_MemClr_which_implies_wit_1.

End VC_Correct.
