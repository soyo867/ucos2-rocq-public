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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_alloc_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmr_Alloc -----*)

Definition OSTmr_Alloc_safety_wit_1 := 
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head <> 0)) ,
  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Alloc_safety_wit_2 := 
forall (frame: Assertion) (free: Z) (used: Z) (head: Z) (PreH1 : (head = 0)) ,
  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Alloc_safety_wit_3 := 
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head = 0)) (PreH2 : (head <> 0)) ,
  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev)
  **  (frame )
|--
  “ False ”
.

Definition OSTmr_Alloc_safety_wit_4 := 
forall (frame: Assertion) (free: Z) (used: Z) (head: Z) (PreH1 : (head <> 0)) (PreH2 : (head = 0)) ,
  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  (frame )
|--
  “ False ”
.

Definition OSTmr_Alloc_safety_wit_5 := 
forall (frame: Assertion) (free: Z) (used: Z) (head: Z) (PreH1 : (head = 0)) (PreH2 : (head = 0)) ,
  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Alloc_safety_wit_6 := 
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head <> 0)) (PreH2 : (head <> 0)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> next)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Alloc_safety_wit_7 := 
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head <> 0)) (PreH2 : (head <> 0)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> next)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Alloc_return_wit_1 := 
(
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head <> 0)) (PreH2 : (head <> 0)) ,
  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> next)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> (unsigned_last_nbits ((used + 1 )) (16)))
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> (unsigned_last_nbits ((free - 1 )) (16)))
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  (frame )
|--
  (tmr_alloc_low_post head next prev used free head )
  **  (frame )
) \/
(
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head <> 0)) (PreH2 : (head <> 0)) ,
  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> next)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> (unsigned_last_nbits ((used + 1 )) (16)))
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> (unsigned_last_nbits ((free - 1 )) (16)))
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  (frame )
|--
  (tmr_alloc_low_post head next prev used free head )
  **  (frame )
).

Definition OSTmr_Alloc_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head <> 0)) (PreH2 : (head <> 0)) ,
  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> next)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> (unsigned_last_nbits ((used + 1 )) (16)))
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> (unsigned_last_nbits ((free - 1 )) (16)))
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  (frame )
|--
  (tmr_alloc_low_post head next prev used free head )
  **  (frame )
.

Definition OSTmr_Alloc_return_wit_2 := 
(
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head = 0)) (PreH2 : (head = 0)) ,
  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  (frame )
|--
  (tmr_alloc_low_post head next prev used free 0 )
  **  (frame )
) \/
(
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head = 0)) (PreH2 : (head = 0)) ,
  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  (frame )
|--
  (tmr_alloc_low_post head next prev used free 0 )
  **  (frame )
).

Definition OSTmr_Alloc_return_wit_2_split_goal_spatial := 
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) (PreH1 : (head = 0)) (PreH2 : (head = 0)) ,
  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  (frame )
|--
  (tmr_alloc_low_post head next prev used free 0 )
  **  (frame )
.

Definition OSTmr_Alloc_partial_solve_wit_1 := 
forall (frame: Assertion) (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) ,
  (tmr_alloc_low_pre head next prev used free )
  **  (frame )
|--
  (tmr_alloc_low_pre head next prev used free )
  **  (frame )
.

Definition OSTmr_Alloc_which_implies_wit_1 := 
forall (free: Z) (used: Z) (prev: Z) (next: Z) (head: Z) ,
  (tmr_alloc_low_pre head next prev used free )
|--
  (“ (head <> 0) ”
  &&  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next)
  **  ((&((head)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev))
  ||
  (“ (head = 0) ”
  &&  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> head)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> used)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> free))
.

Module Type VC_Correct.


Axiom proof_of_OSTmr_Alloc_safety_wit_1 : OSTmr_Alloc_safety_wit_1.
Axiom proof_of_OSTmr_Alloc_safety_wit_2 : OSTmr_Alloc_safety_wit_2.
Axiom proof_of_OSTmr_Alloc_safety_wit_3 : OSTmr_Alloc_safety_wit_3.
Axiom proof_of_OSTmr_Alloc_safety_wit_4 : OSTmr_Alloc_safety_wit_4.
Axiom proof_of_OSTmr_Alloc_safety_wit_5 : OSTmr_Alloc_safety_wit_5.
Axiom proof_of_OSTmr_Alloc_safety_wit_6 : OSTmr_Alloc_safety_wit_6.
Axiom proof_of_OSTmr_Alloc_safety_wit_7 : OSTmr_Alloc_safety_wit_7.
Axiom proof_of_OSTmr_Alloc_return_wit_1 : OSTmr_Alloc_return_wit_1.
Axiom proof_of_OSTmr_Alloc_return_wit_2 : OSTmr_Alloc_return_wit_2.
Axiom proof_of_OSTmr_Alloc_partial_solve_wit_1 : OSTmr_Alloc_partial_solve_wit_1.
Axiom proof_of_OSTmr_Alloc_which_implies_wit_1 : OSTmr_Alloc_which_implies_wit_1.

End VC_Correct.
