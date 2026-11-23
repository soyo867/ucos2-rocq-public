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
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.memory.spec.mem_init_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_MemInit -----*)

Definition OS_MemInit_safety_wit_1 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))) (PreH6 : (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (mem_init_profile sg )) (PreH8 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout sg )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_pre (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_MemInit_safety_wit_2 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) (PreH7 : ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) (PreH8 : (i < (5 - 1 ))) (PreH9 : (mem_init_profile sg )) (PreH10 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH11 : (mem_init_layout sg )) (PreH12 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH13 : (0 <= i)) (PreH14 : (i <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "i" ) )) # UShort  |-> i)
  **  ((( &( "pmem" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (( &( "OSMemTbl" ) ) + ((i + 1 ) * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_MemInit_safety_wit_3 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (i = 4)) (PreH6 : ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) (PreH7 : (i >= (5 - 1 ))) (PreH8 : (mem_init_profile sg )) (PreH9 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH10 : (mem_init_layout sg )) (PreH11 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH12 : (0 <= i)) (PreH13 : (i <= 4)) ,
  ((( &( "i" ) )) # UShort  |-> i)
  **  ((( &( "pmem" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_MemInit_safety_wit_4 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (i = 4)) (PreH6 : ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) (PreH7 : (i >= (5 - 1 ))) (PreH8 : (mem_init_profile sg )) (PreH9 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH10 : (mem_init_layout sg )) (PreH11 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH12 : (0 <= i)) (PreH13 : (i <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "i" ) )) # UShort  |-> i)
  **  ((( &( "pmem" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_MemInit_safety_wit_5 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (mem_init_profile sg )) (PreH6 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH7 : (mem_init_layout sg )) (PreH8 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_MemInit_entail_wit_1 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (mem_init_profile sg )) (PreH6 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH7 : (mem_init_layout sg )) (PreH8 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH9 : (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))) (PreH10 : (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH11 : (mem_init_profile sg )) (PreH12 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH13 : (mem_init_layout sg )) (PreH14 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_entail_wit_2 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) (PreH7 : ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) (PreH8 : (i < (5 - 1 ))) (PreH9 : (mem_init_profile sg )) (PreH10 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH11 : (mem_init_layout sg )) (PreH12 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH13 : (0 <= i)) (PreH14 : (i <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "pmem" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (( &( "OSMemTbl" ) ) + ((i + 1 ) * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) (i + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "pmem" ) )) # Ptr  |->_)
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) (PreH7 : (i < (5 - 1 ))) (PreH8 : (mem_init_profile sg )) (PreH9 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH10 : (mem_init_layout sg )) (PreH11 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH12 : (0 <= i)) (PreH13 : (i <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (( &( "OSMemTbl" ) ) + ((i + 1 ) * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  (mem_init_loop_state sg (LitMap (("?"%string))) (i + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_MemInit_entail_wit_2_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) (PreH7 : (i < (5 - 1 ))) (PreH8 : (mem_init_profile sg )) (PreH9 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH10 : (mem_init_layout sg )) (PreH11 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH12 : (0 <= i)) (PreH13 : (i <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> (( &( "OSMemTbl" ) ) + ((i + 1 ) * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  (mem_init_loop_state sg (LitMap (("?"%string))) (i + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_entail_wit_3 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) (i + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 4) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) (i + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_entail_wit_4 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (i = 4)) (PreH6 : ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) (PreH7 : (i >= (5 - 1 ))) (PreH8 : (mem_init_profile sg )) (PreH9 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH10 : (mem_init_layout sg )) (PreH11 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH12 : (0 <= i)) (PreH13 : (i <= 4)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "i" ) )) # UShort  |-> i)
  **  ((( &( "pmem" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (i = 4)) (PreH6 : (i >= (5 - 1 ))) (PreH7 : (mem_init_profile sg )) (PreH8 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout sg )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH11 : (0 <= i)) (PreH12 : (i <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_MemInit_entail_wit_4_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (i = 4)) (PreH6 : (i >= (5 - 1 ))) (PreH7 : (mem_init_profile sg )) (PreH8 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout sg )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH11 : (0 <= i)) (PreH12 : (i <= 4)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&(((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
  **  (frame )
|--
  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_return_wit_1 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (mem_init_profile sg )) (PreH6 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH7 : (mem_init_layout sg )) (PreH8 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_init_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (mem_init_profile sg )) (PreH6 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH7 : (mem_init_layout sg )) (PreH8 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (mem_init_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_MemInit_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (mem_init_profile sg )) (PreH6 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH7 : (mem_init_layout sg )) (PreH8 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (mem_init_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_partial_solve_wit_1_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  (mem_init_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
.

Definition OS_MemInit_partial_solve_wit_1_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_init_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_partial_solve_wit_1 := OS_MemInit_partial_solve_wit_1_pure -> OS_MemInit_partial_solve_wit_1_aux.

Definition OS_MemInit_partial_solve_wit_2_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))) (PreH6 : (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (mem_init_profile sg )) (PreH8 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout sg )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_pre (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= (sizeof( "os_mem" ) * 5)) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) <= 65535) ” 
  &&  “ (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" )))) ” 
  &&  “ (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_MemInit_partial_solve_wit_2_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))) (PreH6 : (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (mem_init_profile sg )) (PreH8 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout sg )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_pre (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= (sizeof( "os_mem" ) * 5)) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) <= 65535) ” 
  &&  “ (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" )))) ” 
  &&  “ (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" )))) ” 
  &&  “ (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_clr_pre (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_partial_solve_wit_2 := OS_MemInit_partial_solve_wit_2_pure -> OS_MemInit_partial_solve_wit_2_aux.

Definition OS_MemInit_partial_solve_wit_3_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))) (PreH6 : (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (mem_init_profile sg )) (PreH8 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout sg )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_post (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
.

Definition OS_MemInit_partial_solve_wit_3_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))))) (PreH6 : (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (mem_init_profile sg )) (PreH8 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH9 : (mem_init_layout sg )) (PreH10 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_post (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" )))) ” 
  &&  “ (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_clr_post (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_partial_solve_wit_3 := OS_MemInit_partial_solve_wit_3_pure -> OS_MemInit_partial_solve_wit_3_aux.

Definition OS_MemInit_partial_solve_wit_4_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (i < (5 - 1 ))) (PreH2 : (mem_init_profile sg )) (PreH3 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH4 : (mem_init_layout sg )) (PreH5 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH6 : (0 <= i)) (PreH7 : (i <= 4)) ,
  ((( &( "i" ) )) # UShort  |-> i)
  **  (mem_init_loop_state sg (LitMap (("?"%string))) i )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "pmem" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" )))) ”
.

Definition OS_MemInit_partial_solve_wit_4_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (i < (5 - 1 ))) (PreH2 : (mem_init_profile sg )) (PreH3 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH4 : (mem_init_layout sg )) (PreH5 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH6 : (0 <= i)) (PreH7 : (i <= 4)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" )))) ” 
  &&  “ (i < (5 - 1 )) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) i )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_partial_solve_wit_4 := OS_MemInit_partial_solve_wit_4_pure -> OS_MemInit_partial_solve_wit_4_aux.

Definition OS_MemInit_partial_solve_wit_5_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (i >= (5 - 1 ))) (PreH2 : (mem_init_profile sg )) (PreH3 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH4 : (mem_init_layout sg )) (PreH5 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH6 : (0 <= i)) (PreH7 : (i <= 4)) ,
  ((( &( "i" ) )) # UShort  |-> i)
  **  (mem_init_loop_state sg (LitMap (("?"%string))) i )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "pmem" ) )) # Ptr  |-> (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" )))) ”
.

Definition OS_MemInit_partial_solve_wit_5_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (PreH1 : (i >= (5 - 1 ))) (PreH2 : (mem_init_profile sg )) (PreH3 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH4 : (mem_init_layout sg )) (PreH5 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH6 : (0 <= i)) (PreH7 : (i <= 4)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (4 <= i) ” 
  &&  “ (i <= 4) ” 
  &&  “ ((( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))) = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" )))) ” 
  &&  “ (i >= (5 - 1 )) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 4) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) i )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_partial_solve_wit_5 := OS_MemInit_partial_solve_wit_5_pure -> OS_MemInit_partial_solve_wit_5_aux.

Definition OS_MemInit_partial_solve_wit_6_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |->_)
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
.

Definition OS_MemInit_partial_solve_wit_6_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_MemInit_partial_solve_wit_6 := OS_MemInit_partial_solve_wit_6_pure -> OS_MemInit_partial_solve_wit_6_aux.

Definition OS_MemInit_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_pre sg )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" )))) ” 
  &&  “ (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (mem_clr_pre (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
) \/
(
forall (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_pre sg )
|--
  EX (x: Z) ,
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" )))) ” 
  &&  “ (((( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) + ((sizeof( "os_mem" ) * 5) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  ((( &( "OSMemFreeList" ) )) # Ptr  |-> x)
  **  (mem_clr_pre (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
).

Definition OS_MemInit_which_implies_wit_2 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_post (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_init_loop_state sg (LitMap (("?"%string))) 0 )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_post (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
|--
  (mem_init_loop_state sg (LitMap (("?"%string))) 0 )
).

Definition OS_MemInit_which_implies_wit_2_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_clr_post (( &( "OSMemTbl" ) ) + (0 * sizeof( "os_mem" ))) (sizeof( "os_mem" ) * 5) )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
|--
  (mem_init_loop_state sg (LitMap (("?"%string))) 0 )
.

Definition OS_MemInit_which_implies_wit_3 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (pmem: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) (PreH7 : (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" )))) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (pmem: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) (PreH7 : (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
|--
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
).

Definition OS_MemInit_which_implies_wit_3_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (pmem: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (0 <= i)) (PreH6 : (i < 4)) (PreH7 : (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
|--
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
.

Definition OS_MemInit_which_implies_wit_4 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (pmem: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (4 <= i)) (PreH6 : (i <= 4)) (PreH7 : (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ” 
  &&  “ (i = 4) ” 
  &&  “ (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" )))) ”
  &&  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (pmem: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (4 <= i)) (PreH6 : (i <= 4)) (PreH7 : (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
|--
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
).

Definition OS_MemInit_which_implies_wit_4_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (i: Z) (pmem: Z) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) (PreH5 : (4 <= i)) (PreH6 : (i <= 4)) (PreH7 : (pmem = (( &( "OSMemTbl" ) ) + (i * sizeof( "os_mem" ))))) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) i )
|--
  ((&((pmem)  # "os_mem" ->ₛ "OSMemFreeList")) # Ptr  |-> 0)
  **  ((&((pmem)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> 0)
  **  (mem_init_loop_residual sg (LitMap (("?"%string))) i )
.

Definition OS_MemInit_which_implies_wit_5 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
|--
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  (mem_init_prefix sg (LitMap (("?"%string))) 5 )
  **  ((( &( "OSMemFreeList" ) )) # Ptr  |->_)
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : (mem_init_profile sg )) (PreH2 : (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) )) (PreH3 : (mem_init_layout sg )) (PreH4 : ((sizeof( "os_mem" ) * 5) = 120)) ,
  (mem_init_loop_state sg (LitMap (("?"%string))) 5 )
|--
  EX (x: Z) ,
  “ (mem_init_profile sg ) ” 
  &&  “ (mem_init_global_addresses sg ( &( "OSMemTbl" ) ) ( &( "OSMemFreeList" ) ) ) ” 
  &&  “ (mem_init_layout sg ) ” 
  &&  “ ((sizeof( "os_mem" ) * 5) = 120) ”
  &&  ((( &( "OSMemFreeList" ) )) # Ptr  |-> x)
  **  (mem_init_prefix sg (LitMap (("?"%string))) 5 )
).

Module Type VC_Correct.


Axiom proof_of_OS_MemInit_safety_wit_1 : OS_MemInit_safety_wit_1.
Axiom proof_of_OS_MemInit_safety_wit_2 : OS_MemInit_safety_wit_2.
Axiom proof_of_OS_MemInit_safety_wit_3 : OS_MemInit_safety_wit_3.
Axiom proof_of_OS_MemInit_safety_wit_4 : OS_MemInit_safety_wit_4.
Axiom proof_of_OS_MemInit_safety_wit_5 : OS_MemInit_safety_wit_5.
Axiom proof_of_OS_MemInit_entail_wit_1 : OS_MemInit_entail_wit_1.
Axiom proof_of_OS_MemInit_entail_wit_2 : OS_MemInit_entail_wit_2.
Axiom proof_of_OS_MemInit_entail_wit_3 : OS_MemInit_entail_wit_3.
Axiom proof_of_OS_MemInit_entail_wit_4 : OS_MemInit_entail_wit_4.
Axiom proof_of_OS_MemInit_return_wit_1 : OS_MemInit_return_wit_1.
Axiom proof_of_OS_MemInit_partial_solve_wit_1_pure : OS_MemInit_partial_solve_wit_1_pure.
Axiom proof_of_OS_MemInit_partial_solve_wit_1 : OS_MemInit_partial_solve_wit_1.
Axiom proof_of_OS_MemInit_partial_solve_wit_2_pure : OS_MemInit_partial_solve_wit_2_pure.
Axiom proof_of_OS_MemInit_partial_solve_wit_2 : OS_MemInit_partial_solve_wit_2.
Axiom proof_of_OS_MemInit_partial_solve_wit_3_pure : OS_MemInit_partial_solve_wit_3_pure.
Axiom proof_of_OS_MemInit_partial_solve_wit_3 : OS_MemInit_partial_solve_wit_3.
Axiom proof_of_OS_MemInit_partial_solve_wit_4_pure : OS_MemInit_partial_solve_wit_4_pure.
Axiom proof_of_OS_MemInit_partial_solve_wit_4 : OS_MemInit_partial_solve_wit_4.
Axiom proof_of_OS_MemInit_partial_solve_wit_5_pure : OS_MemInit_partial_solve_wit_5_pure.
Axiom proof_of_OS_MemInit_partial_solve_wit_5 : OS_MemInit_partial_solve_wit_5.
Axiom proof_of_OS_MemInit_partial_solve_wit_6_pure : OS_MemInit_partial_solve_wit_6_pure.
Axiom proof_of_OS_MemInit_partial_solve_wit_6 : OS_MemInit_partial_solve_wit_6.
Axiom proof_of_OS_MemInit_which_implies_wit_1 : OS_MemInit_which_implies_wit_1.
Axiom proof_of_OS_MemInit_which_implies_wit_2 : OS_MemInit_which_implies_wit_2.
Axiom proof_of_OS_MemInit_which_implies_wit_3 : OS_MemInit_which_implies_wit_3.
Axiom proof_of_OS_MemInit_which_implies_wit_4 : OS_MemInit_which_implies_wit_4.
Axiom proof_of_OS_MemInit_which_implies_wit_5 : OS_MemInit_which_implies_wit_5.

End VC_Correct.
