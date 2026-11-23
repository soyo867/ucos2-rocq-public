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
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

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


Axiom proof_of_OS_MemClr_safety_wit_1 : OS_MemClr_safety_wit_1.
Axiom proof_of_OS_MemClr_entail_wit_1 : OS_MemClr_entail_wit_1.
Axiom proof_of_OS_MemClr_entail_wit_2 : OS_MemClr_entail_wit_2.
Axiom proof_of_OS_MemClr_return_wit_1 : OS_MemClr_return_wit_1.
Axiom proof_of_OS_MemClr_partial_solve_wit_1_pure : OS_MemClr_partial_solve_wit_1_pure.
Axiom proof_of_OS_MemClr_partial_solve_wit_1 : OS_MemClr_partial_solve_wit_1.
Axiom proof_of_OS_MemClr_which_implies_wit_1 : OS_MemClr_which_implies_wit_1.

End VC_Correct.
