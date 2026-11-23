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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_FlagInit -----*)

Definition OS_FlagInit_safety_wit_1 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))) (PreH6 : (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (flag_init_profile sg )) (PreH8 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flag_init_layout sg )) (PreH10 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_pre (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagInit_safety_wit_2 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) (PreH7 : ((ix + 1 ) = (ix + 1 ))) (PreH8 : ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH9 : ((( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))) (PreH10 : (ix < (5 - 1 ))) (PreH11 : (flag_init_profile sg )) (PreH12 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (flag_init_layout sg )) (PreH14 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH15 : (0 <= ix)) (PreH16 : (ix <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pgrp1" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))
  **  ((( &( "pgrp2" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagInit_safety_wit_3 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (ix = 4)) (PreH6 : ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH7 : (ix >= (5 - 1 ))) (PreH8 : (flag_init_profile sg )) (PreH9 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_init_layout sg )) (PreH11 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 4)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pgrp1" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagInit_safety_wit_4 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (ix = 4)) (PreH6 : ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH7 : (ix >= (5 - 1 ))) (PreH8 : (flag_init_profile sg )) (PreH9 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_init_layout sg )) (PreH11 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pgrp1" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagInit_safety_wit_5 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (flag_init_profile sg )) (PreH6 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout sg )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_FlagInit_entail_wit_1 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (flag_init_profile sg )) (PreH6 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout sg )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH9 : (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))) (PreH10 : (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (flag_init_profile sg )) (PreH12 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (flag_init_layout sg )) (PreH14 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_entail_wit_2 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) (PreH7 : ((ix + 1 ) = (ix + 1 ))) (PreH8 : ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH9 : ((( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))) (PreH10 : (ix < (5 - 1 ))) (PreH11 : (flag_init_profile sg )) (PreH12 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH13 : (flag_init_layout sg )) (PreH14 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH15 : (0 <= ix)) (PreH16 : (ix <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pgrp1" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))
  **  ((( &( "pgrp2" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 4) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) (PreH7 : (ix < (5 - 1 ))) (PreH8 : (flag_init_profile sg )) (PreH9 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_init_layout sg )) (PreH11 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  (flag_init_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_FlagInit_entail_wit_2_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) (PreH7 : (ix < (5 - 1 ))) (PreH8 : (flag_init_profile sg )) (PreH9 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_init_layout sg )) (PreH11 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  (flag_init_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_entail_wit_3 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= (ix + 1 )) ” 
  &&  “ ((ix + 1 ) <= 4) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_entail_wit_4 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (ix = 4)) (PreH6 : ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH7 : (ix >= (5 - 1 ))) (PreH8 : (flag_init_profile sg )) (PreH9 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH10 : (flag_init_layout sg )) (PreH11 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH12 : (0 <= ix)) (PreH13 : (ix <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pgrp1" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (ix = 4)) (PreH6 : (ix >= (5 - 1 ))) (PreH7 : (flag_init_profile sg )) (PreH8 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flag_init_layout sg )) (PreH10 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_FlagInit_entail_wit_4_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (ix = 4)) (PreH6 : (ix >= (5 - 1 ))) (PreH7 : (flag_init_profile sg )) (PreH8 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flag_init_layout sg )) (PreH10 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_return_wit_1 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (flag_init_profile sg )) (PreH6 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout sg )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (flag_init_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (flag_init_profile sg )) (PreH6 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout sg )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (flag_init_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_FlagInit_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (flag_init_profile sg )) (PreH6 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH7 : (flag_init_layout sg )) (PreH8 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (flag_init_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_partial_solve_wit_1_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  ((( &( "pgrp2" ) )) # Ptr  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (flag_init_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
.

Definition OS_FlagInit_partial_solve_wit_1_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (flag_init_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_partial_solve_wit_1 := OS_FlagInit_partial_solve_wit_1_pure -> OS_FlagInit_partial_solve_wit_1_aux.

Definition OS_FlagInit_partial_solve_wit_2_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))) (PreH6 : (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (flag_init_profile sg )) (PreH8 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flag_init_layout sg )) (PreH10 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_pre (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= (sizeof( "os_flag_grp" ) * 5)) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) <= 65535) ” 
  &&  “ (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" )))) ” 
  &&  “ (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_FlagInit_partial_solve_wit_2_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))) (PreH6 : (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (flag_init_profile sg )) (PreH8 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flag_init_layout sg )) (PreH10 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_pre (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= (sizeof( "os_flag_grp" ) * 5)) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) <= 65535) ” 
  &&  “ (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" )))) ” 
  &&  “ (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" )))) ” 
  &&  “ (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (mem_clr_pre (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_partial_solve_wit_2 := OS_FlagInit_partial_solve_wit_2_pure -> OS_FlagInit_partial_solve_wit_2_aux.

Definition OS_FlagInit_partial_solve_wit_3_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))) (PreH6 : (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (flag_init_profile sg )) (PreH8 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flag_init_layout sg )) (PreH10 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_post (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
.

Definition OS_FlagInit_partial_solve_wit_3_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))))) (PreH6 : (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (flag_init_profile sg )) (PreH8 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH9 : (flag_init_layout sg )) (PreH10 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_post (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" )))) ” 
  &&  “ (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (mem_clr_post (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_partial_solve_wit_3 := OS_FlagInit_partial_solve_wit_3_pure -> OS_FlagInit_partial_solve_wit_3_aux.

Definition OS_FlagInit_partial_solve_wit_4_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < (5 - 1 ))) (PreH2 : (flag_init_profile sg )) (PreH3 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH4 : (flag_init_layout sg )) (PreH5 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 4)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pgrp1" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))
  **  ((( &( "pgrp2" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))))
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 4) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" )))) ” 
  &&  “ ((( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" )))) ”
.

Definition OS_FlagInit_partial_solve_wit_4_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < (5 - 1 ))) (PreH2 : (flag_init_profile sg )) (PreH3 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH4 : (flag_init_layout sg )) (PreH5 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 4)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 4) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" )))) ” 
  &&  “ ((( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + ((ix + 1 ) * sizeof( "os_flag_grp" )))) ” 
  &&  “ (ix < (5 - 1 )) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 4) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_partial_solve_wit_4 := OS_FlagInit_partial_solve_wit_4_pure -> OS_FlagInit_partial_solve_wit_4_aux.

Definition OS_FlagInit_partial_solve_wit_5_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= (5 - 1 ))) (PreH2 : (flag_init_profile sg )) (PreH3 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH4 : (flag_init_layout sg )) (PreH5 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 4)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |-> (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (4 <= ix) ” 
  &&  “ (ix <= 4) ” 
  &&  “ ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" )))) ”
.

Definition OS_FlagInit_partial_solve_wit_5_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= (5 - 1 ))) (PreH2 : (flag_init_profile sg )) (PreH3 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH4 : (flag_init_layout sg )) (PreH5 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH6 : (0 <= ix)) (PreH7 : (ix <= 4)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (4 <= ix) ” 
  &&  “ (ix <= 4) ” 
  &&  “ ((( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))) = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" )))) ” 
  &&  “ (ix >= (5 - 1 )) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 4) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_partial_solve_wit_5 := OS_FlagInit_partial_solve_wit_5_pure -> OS_FlagInit_partial_solve_wit_5_aux.

Definition OS_FlagInit_partial_solve_wit_6_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pgrp1" ) )) # Ptr  |->_)
  **  ((( &( "pgrp2" ) )) # Ptr  |->_)
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
.

Definition OS_FlagInit_partial_solve_wit_6_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_FlagInit_partial_solve_wit_6 := OS_FlagInit_partial_solve_wit_6_pure -> OS_FlagInit_partial_solve_wit_6_aux.

Definition OS_FlagInit_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_pre sg )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" )))) ” 
  &&  “ (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (mem_clr_pre (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
) \/
(
forall (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_pre sg )
|--
  EX (x: Z) ,
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" )))) ” 
  &&  “ (((( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) + ((sizeof( "os_flag_grp" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> x)
  **  (mem_clr_pre (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
).

Definition OS_FlagInit_which_implies_wit_2 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_post (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (flag_init_loop_state sg (LitMap (("?"%string))) 0 )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_post (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
|--
  (flag_init_loop_state sg (LitMap (("?"%string))) 0 )
).

Definition OS_FlagInit_which_implies_wit_2_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (mem_clr_post (( &( "OSFlagTbl" ) ) + (0 * sizeof( "os_flag_grp" ))) (sizeof( "os_flag_grp" ) * 5) )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
|--
  (flag_init_loop_state sg (LitMap (("?"%string))) 0 )
.

Definition OS_FlagInit_which_implies_wit_3 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (pgrp1: Z) (pgrp2: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) (PreH7 : (ix_next = (ix + 1 ))) (PreH8 : (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH9 : (pgrp2 = (( &( "OSFlagTbl" ) ) + (ix_next * sizeof( "os_flag_grp" ))))) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 4) ” 
  &&  “ (ix_next = (ix + 1 )) ” 
  &&  “ (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" )))) ” 
  &&  “ (pgrp2 = (( &( "OSFlagTbl" ) ) + (ix_next * sizeof( "os_flag_grp" )))) ”
  &&  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (pgrp1: Z) (pgrp2: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) (PreH7 : (ix_next = (ix + 1 ))) (PreH8 : (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH9 : (pgrp2 = (( &( "OSFlagTbl" ) ) + (ix_next * sizeof( "os_flag_grp" ))))) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
).

Definition OS_FlagInit_which_implies_wit_3_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (pgrp1: Z) (pgrp2: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (0 <= ix)) (PreH6 : (ix < 4)) (PreH7 : (ix_next = (ix + 1 ))) (PreH8 : (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) (PreH9 : (pgrp2 = (( &( "OSFlagTbl" ) ) + (ix_next * sizeof( "os_flag_grp" ))))) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
.

Definition OS_FlagInit_which_implies_wit_4 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (pgrp1: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (4 <= ix)) (PreH6 : (ix <= 4)) (PreH7 : (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ” 
  &&  “ (ix = 4) ” 
  &&  “ (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" )))) ”
  &&  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (pgrp1: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (4 <= ix)) (PreH6 : (ix <= 4)) (PreH7 : (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
).

Definition OS_FlagInit_which_implies_wit_4_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (pgrp1: Z) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) (PreH5 : (4 <= ix)) (PreH6 : (ix <= 4)) (PreH7 : (pgrp1 = (( &( "OSFlagTbl" ) ) + (ix * sizeof( "os_flag_grp" ))))) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagType")) # UChar  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagWaitList")) # Ptr  |-> 0)
  **  ((&((pgrp1)  # "os_flag_grp" ->ₛ "OSFlagName")) # Ptr  |-> 0)
  **  (flag_init_loop_residual sg (LitMap (("?"%string))) ix )
.

Definition OS_FlagInit_which_implies_wit_5 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
|--
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  (flag_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSFlagFreeList" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (flag_init_profile sg )) (PreH2 : (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) )) (PreH3 : (flag_init_layout sg )) (PreH4 : ((sizeof( "os_flag_grp" ) * 5) = 80)) ,
  (flag_init_loop_state sg (LitMap (("?"%string))) 5 )
|--
  EX (x: Z) ,
  “ (flag_init_profile sg ) ” 
  &&  “ (flag_init_global_addresses sg ( &( "OSFlagTbl" ) ) ( &( "OSFlagFreeList" ) ) ) ” 
  &&  “ (flag_init_layout sg ) ” 
  &&  “ ((sizeof( "os_flag_grp" ) * 5) = 80) ”
  &&  ((( &( "OSFlagFreeList" ) )) # Ptr  |-> x)
  **  (flag_init_prefix sg (LitMap (("?"%string))) 5 )
).

Module Type VC_Correct.


Axiom proof_of_OS_FlagInit_safety_wit_1 : OS_FlagInit_safety_wit_1.
Axiom proof_of_OS_FlagInit_safety_wit_2 : OS_FlagInit_safety_wit_2.
Axiom proof_of_OS_FlagInit_safety_wit_3 : OS_FlagInit_safety_wit_3.
Axiom proof_of_OS_FlagInit_safety_wit_4 : OS_FlagInit_safety_wit_4.
Axiom proof_of_OS_FlagInit_safety_wit_5 : OS_FlagInit_safety_wit_5.
Axiom proof_of_OS_FlagInit_entail_wit_1 : OS_FlagInit_entail_wit_1.
Axiom proof_of_OS_FlagInit_entail_wit_2 : OS_FlagInit_entail_wit_2.
Axiom proof_of_OS_FlagInit_entail_wit_3 : OS_FlagInit_entail_wit_3.
Axiom proof_of_OS_FlagInit_entail_wit_4 : OS_FlagInit_entail_wit_4.
Axiom proof_of_OS_FlagInit_return_wit_1 : OS_FlagInit_return_wit_1.
Axiom proof_of_OS_FlagInit_partial_solve_wit_1_pure : OS_FlagInit_partial_solve_wit_1_pure.
Axiom proof_of_OS_FlagInit_partial_solve_wit_1 : OS_FlagInit_partial_solve_wit_1.
Axiom proof_of_OS_FlagInit_partial_solve_wit_2_pure : OS_FlagInit_partial_solve_wit_2_pure.
Axiom proof_of_OS_FlagInit_partial_solve_wit_2 : OS_FlagInit_partial_solve_wit_2.
Axiom proof_of_OS_FlagInit_partial_solve_wit_3_pure : OS_FlagInit_partial_solve_wit_3_pure.
Axiom proof_of_OS_FlagInit_partial_solve_wit_3 : OS_FlagInit_partial_solve_wit_3.
Axiom proof_of_OS_FlagInit_partial_solve_wit_4_pure : OS_FlagInit_partial_solve_wit_4_pure.
Axiom proof_of_OS_FlagInit_partial_solve_wit_4 : OS_FlagInit_partial_solve_wit_4.
Axiom proof_of_OS_FlagInit_partial_solve_wit_5_pure : OS_FlagInit_partial_solve_wit_5_pure.
Axiom proof_of_OS_FlagInit_partial_solve_wit_5 : OS_FlagInit_partial_solve_wit_5.
Axiom proof_of_OS_FlagInit_partial_solve_wit_6_pure : OS_FlagInit_partial_solve_wit_6_pure.
Axiom proof_of_OS_FlagInit_partial_solve_wit_6 : OS_FlagInit_partial_solve_wit_6.
Axiom proof_of_OS_FlagInit_which_implies_wit_1 : OS_FlagInit_which_implies_wit_1.
Axiom proof_of_OS_FlagInit_which_implies_wit_2 : OS_FlagInit_which_implies_wit_2.
Axiom proof_of_OS_FlagInit_which_implies_wit_3 : OS_FlagInit_which_implies_wit_3.
Axiom proof_of_OS_FlagInit_which_implies_wit_4 : OS_FlagInit_which_implies_wit_4.
Axiom proof_of_OS_FlagInit_which_implies_wit_5 : OS_FlagInit_which_implies_wit_5.

End VC_Correct.
