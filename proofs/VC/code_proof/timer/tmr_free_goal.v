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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_free_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmr_Free -----*)

Definition OSTmr_Free_safety_wit_1 := 
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used_write_spec)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free_write_spec)
  **  (GlobalStrings LitMap_write_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Free_safety_wit_2 := 
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used_write_spec)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free_write_spec)
  **  (GlobalStrings LitMap_write_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Free_safety_wit_3 := 
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) ,
  (store_stringLit (LitMap_write_spec (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap_write_spec (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used_write_spec)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free_write_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Free_safety_wit_4 := 
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) ,
  (store_stringLit (LitMap_write_spec (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap_write_spec (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap_write_spec (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used_write_spec)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free_write_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Free_return_wit_1 := 
(
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) ,
  (store_stringLit (LitMap_write_spec (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap_write_spec (cons (("?"%string)) ((@nil string))) )
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap_write_spec (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> (unsigned_last_nbits ((used_write_spec - 1 )) (16)))
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> (unsigned_last_nbits ((free_write_spec + 1 )) (16)))
|--
  (tmr_free_write_post ptmr_pre root_write_spec used_write_spec free_write_spec (LitMap_write_spec (("?"%string))) )
  **  (GlobalStrings LitMap_write_spec )
) \/
(
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) ,
  (GlobalStrings LitMap_write_spec )
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap_write_spec (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> (unsigned_last_nbits ((used_write_spec - 1 )) (16)))
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> (unsigned_last_nbits ((free_write_spec + 1 )) (16)))
|--
  (tmr_free_write_post ptmr_pre root_write_spec used_write_spec free_write_spec (LitMap_write_spec (("?"%string))) )
  **  (GlobalStrings LitMap_write_spec )
).

Definition OSTmr_Free_return_wit_1_split_goal_spatial := 
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) ,
  (GlobalStrings LitMap_write_spec )
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap_write_spec (("?"%string))) + (0 * sizeof(CHAR))))
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> (unsigned_last_nbits ((used_write_spec - 1 )) (16)))
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> (unsigned_last_nbits ((free_write_spec + 1 )) (16)))
|--
  (tmr_free_write_post ptmr_pre root_write_spec used_write_spec free_write_spec (LitMap_write_spec (("?"%string))) )
  **  (GlobalStrings LitMap_write_spec )
.

Definition OSTmr_Free_partial_solve_wit_1 := 
forall (ptmr_pre: Z) (LitMap_write_spec: (string -> Z)) (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) ,
  (tmr_free_write_pre ptmr_pre root_write_spec used_write_spec free_write_spec )
  **  (GlobalStrings LitMap_write_spec )
|--
  (tmr_free_write_pre ptmr_pre root_write_spec used_write_spec free_write_spec )
  **  (GlobalStrings LitMap_write_spec )
.

Definition OSTmr_Free_which_implies_wit_1 := 
(
forall (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) (ptmr: Z) ,
  (tmr_free_write_pre ptmr root_write_spec used_write_spec free_write_spec )
|--
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used_write_spec)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free_write_spec)
) \/
(
forall (free_write_spec: Z) (used_write_spec: Z) (root_write_spec: Z) (ptmr: Z) ,
  (tmr_free_write_pre ptmr root_write_spec used_write_spec free_write_spec )
|--
  EX (x_9: Z)  (x_8: Z)  (x_7: Z)  (x_6: Z)  (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> x_9)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> x_8)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> x_7)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> x_6)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> x_5)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> x_4)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> x_3)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> x_2)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> x)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> root_write_spec)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used_write_spec)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free_write_spec)
).

Definition OSTmr_Free_derive_raw_spec_by_write_spec := 
forall (ptmr_pre: Z) (LitMap_raw_spec: (string -> Z)) (free_raw_spec: Z) (used_raw_spec: Z) (root_raw_spec: Z) (old_raw_spec: TimerImage) ,
  (tmr_free_pre ptmr_pre old_raw_spec root_raw_spec used_raw_spec free_raw_spec )
  **  (GlobalStrings LitMap_raw_spec )
|--
EX (root_write_spec: Z) (used_write_spec: Z) (free_write_spec: Z) (LitMap_write_spec: (string -> Z)) ,
  ((tmr_free_write_pre ptmr_pre root_write_spec used_write_spec free_write_spec )
  **  (GlobalStrings LitMap_write_spec ))
  **
  (((tmr_free_write_post ptmr_pre root_write_spec used_write_spec free_write_spec (LitMap_write_spec (("?"%string))) )
  **  (GlobalStrings LitMap_write_spec ))
  -*
  ((tmr_free_post ptmr_pre old_raw_spec root_raw_spec used_raw_spec free_raw_spec (LitMap_raw_spec (("?"%string))) )
  **  (GlobalStrings LitMap_raw_spec )))
.

Definition OSTmr_Free_derive_valid_pool_spec_by_raw_spec := 
forall (ptmr_pre: Z) (LitMap_valid_pool_spec: (string -> Z)) (old_valid_pool_spec: TimerImage) (t_valid_pool_spec: TimerObjectState) (i_valid_pool_spec: Z) (s_valid_pool_spec: GlobTimerState) (sg_valid_pool_spec: StableGlobVars) ,
  “ (tmr_free_valid_input sg_valid_pool_spec s_valid_pool_spec i_valid_pool_spec t_valid_pool_spec old_valid_pool_spec ptmr_pre ) ”
  &&  (timer_inv sg_valid_pool_spec s_valid_pool_spec )
  **  (GlobalStrings LitMap_valid_pool_spec )
|--
EX (old_raw_spec: TimerImage) (root_raw_spec: Z) (used_raw_spec: Z) (free_raw_spec: Z) (LitMap_raw_spec: (string -> Z)) ,
  ((tmr_free_pre ptmr_pre old_raw_spec root_raw_spec used_raw_spec free_raw_spec )
  **  (GlobalStrings LitMap_raw_spec ))
  **
  (((tmr_free_post ptmr_pre old_raw_spec root_raw_spec used_raw_spec free_raw_spec (LitMap_raw_spec (("?"%string))) )
  **  (GlobalStrings LitMap_raw_spec ))
  -*
  ((tmr_free_valid_post sg_valid_pool_spec s_valid_pool_spec i_valid_pool_spec old_valid_pool_spec (LitMap_valid_pool_spec (("?"%string))) )
  **  (GlobalStrings LitMap_valid_pool_spec )))
.

Module Type VC_Correct.


Axiom proof_of_OSTmr_Free_safety_wit_1 : OSTmr_Free_safety_wit_1.
Axiom proof_of_OSTmr_Free_safety_wit_2 : OSTmr_Free_safety_wit_2.
Axiom proof_of_OSTmr_Free_safety_wit_3 : OSTmr_Free_safety_wit_3.
Axiom proof_of_OSTmr_Free_safety_wit_4 : OSTmr_Free_safety_wit_4.
Axiom proof_of_OSTmr_Free_return_wit_1 : OSTmr_Free_return_wit_1.
Axiom proof_of_OSTmr_Free_partial_solve_wit_1 : OSTmr_Free_partial_solve_wit_1.
Axiom proof_of_OSTmr_Free_which_implies_wit_1 : OSTmr_Free_which_implies_wit_1.
Axiom proof_of_OSTmr_Free_derive_raw_spec_by_write_spec : OSTmr_Free_derive_raw_spec_by_write_spec.
Axiom proof_of_OSTmr_Free_derive_valid_pool_spec_by_raw_spec : OSTmr_Free_derive_valid_pool_spec_by_raw_spec.

End VC_Correct.
