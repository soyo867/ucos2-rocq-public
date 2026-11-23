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
Require Import Ucos2Verify.VC.code.task.spec.task_stk_clr_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_TaskStkClr -----*)

Definition OS_TaskStkClr_safety_wit_1 := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : ((Zlength (initial)) = size_pre)) (PreH2 : (0 < pbos_pre)) (PreH3 : ((pbos_pre % ( 4 ) ) = 0)) (PreH4 : ((pbos_pre + (size_pre * sizeof(UINT))) <= UINT_MAX)) (PreH5 : (0 < size)) (PreH6 : (size <= size_pre)) (PreH7 : ((pbos_pre + ((size_pre - size ) * sizeof(UINT))) = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) (PreH8 : (0 < (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) (PreH9 : (((pbos_pre + ((size_pre - size ) * sizeof(UINT))) + (1 * sizeof(UINT))) <= UINT_MAX)) (PreH10 : (size > 0)) (PreH11 : (0 <= size)) (PreH12 : (size <= size_pre)) (PreH13 : (size_pre <= UINT_MAX)) (PreH14 : (0 <= opt_pre)) (PreH15 : (opt_pre <= 65535)) (PreH16 : ((Z.land opt_pre 1) <> 0)) (PreH17 : ((Z.land opt_pre 2) <> 0)) (PreH18 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  ((( &( "size" ) )) # UInt  |-> (size - 1 ))
  **  ((( &( "pbos" ) )) # Ptr  |-> (pbos_pre + ((size_pre - size ) * sizeof(UINT))))
  **  (((pbos_pre + ((size_pre - size ) * sizeof(UINT)))) # UInt  |->_)
  **  (task_stk_clr_residual pbos_pre size_pre size initial )
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  (R )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_TaskStkClr_entail_wit_1 := 
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 2) <> 0)) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : (0 <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  “ (0 <= size_pre) ” 
  &&  “ (size_pre <= size_pre) ” 
  &&  “ (size_pre <= UINT_MAX) ” 
  &&  “ (0 <= opt_pre) ” 
  &&  “ (opt_pre <= 65535) ” 
  &&  “ ((Z.land opt_pre 1) <> 0) ” 
  &&  “ ((Z.land opt_pre 2) <> 0) ” 
  &&  “ (pbos_pre = (pbos_pre + ((size_pre - size_pre ) * sizeof(UINT)))) ”
  &&  (task_stk_clr_loop pbos_pre size_pre size_pre initial )
  **  (R )
) \/
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 2) <> 0)) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : (0 <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_loop pbos_pre size_pre size_pre initial )
  **  (R )
).

Definition OS_TaskStkClr_entail_wit_1_split_goal_spatial := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 2) <> 0)) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : (0 <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_loop pbos_pre size_pre size_pre initial )
  **  (R )
.

Definition OS_TaskStkClr_entail_wit_2 := 
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : ((Zlength (initial)) = size_pre)) (PreH2 : (0 < pbos_pre)) (PreH3 : ((pbos_pre % ( 4 ) ) = 0)) (PreH4 : ((pbos_pre + (size_pre * sizeof(UINT))) <= UINT_MAX)) (PreH5 : (0 < size)) (PreH6 : (size <= size_pre)) (PreH7 : ((pbos_pre + ((size_pre - size ) * sizeof(UINT))) = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) (PreH8 : (0 < (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) (PreH9 : (((pbos_pre + ((size_pre - size ) * sizeof(UINT))) + (1 * sizeof(UINT))) <= UINT_MAX)) (PreH10 : (size > 0)) (PreH11 : (0 <= size)) (PreH12 : (size <= size_pre)) (PreH13 : (size_pre <= UINT_MAX)) (PreH14 : (0 <= opt_pre)) (PreH15 : (opt_pre <= 65535)) (PreH16 : ((Z.land opt_pre 1) <> 0)) (PreH17 : ((Z.land opt_pre 2) <> 0)) (PreH18 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (((pbos_pre + ((size_pre - size ) * sizeof(UINT)))) # UInt  |-> 0)
  **  (task_stk_clr_residual pbos_pre size_pre size initial )
  **  (R )
|--
  “ (0 <= (size - 1 )) ” 
  &&  “ ((size - 1 ) <= size_pre) ” 
  &&  “ (size_pre <= UINT_MAX) ” 
  &&  “ (0 <= opt_pre) ” 
  &&  “ (opt_pre <= 65535) ” 
  &&  “ ((Z.land opt_pre 1) <> 0) ” 
  &&  “ ((Z.land opt_pre 2) <> 0) ” 
  &&  “ ((pbos_pre + (((size_pre - size ) + 1 ) * sizeof(UINT))) = (pbos_pre + ((size_pre - (size - 1 ) ) * sizeof(UINT)))) ”
  &&  (task_stk_clr_loop pbos_pre size_pre (size - 1 ) initial )
  **  (R )
) \/
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Zlength (initial)) = size_pre)) (PreH4 : (0 < pbos_pre)) (PreH5 : ((pbos_pre % ( 4 ) ) = 0)) (PreH6 : ((pbos_pre + (size_pre * sizeof(UINT))) <= UINT_MAX)) (PreH7 : (0 < size)) (PreH8 : (size <= size_pre)) (PreH9 : (0 < (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) (PreH10 : (((pbos_pre + ((size_pre - size ) * sizeof(UINT))) + (1 * sizeof(UINT))) <= UINT_MAX)) (PreH11 : (size > 0)) (PreH12 : (0 <= size)) (PreH13 : (size <= size_pre)) (PreH14 : (size_pre <= UINT_MAX)) (PreH15 : (0 <= opt_pre)) (PreH16 : (opt_pre <= 65535)) (PreH17 : ((Z.land opt_pre 1) <> 0)) (PreH18 : ((Z.land opt_pre 2) <> 0)) (PreH19 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (((pbos_pre + ((size_pre - size ) * sizeof(UINT)))) # UInt  |-> 0)
  **  (task_stk_clr_residual pbos_pre size_pre size initial )
  **  (R )
|--
  (task_stk_clr_loop pbos_pre size_pre (size - 1 ) initial )
  **  (R )
).

Definition OS_TaskStkClr_entail_wit_2_split_goal_spatial := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Zlength (initial)) = size_pre)) (PreH4 : (0 < pbos_pre)) (PreH5 : ((pbos_pre % ( 4 ) ) = 0)) (PreH6 : ((pbos_pre + (size_pre * sizeof(UINT))) <= UINT_MAX)) (PreH7 : (0 < size)) (PreH8 : (size <= size_pre)) (PreH9 : (0 < (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) (PreH10 : (((pbos_pre + ((size_pre - size ) * sizeof(UINT))) + (1 * sizeof(UINT))) <= UINT_MAX)) (PreH11 : (size > 0)) (PreH12 : (0 <= size)) (PreH13 : (size <= size_pre)) (PreH14 : (size_pre <= UINT_MAX)) (PreH15 : (0 <= opt_pre)) (PreH16 : (opt_pre <= 65535)) (PreH17 : ((Z.land opt_pre 1) <> 0)) (PreH18 : ((Z.land opt_pre 2) <> 0)) (PreH19 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (((pbos_pre + ((size_pre - size ) * sizeof(UINT)))) # UInt  |-> 0)
  **  (task_stk_clr_residual pbos_pre size_pre size initial )
  **  (R )
|--
  (task_stk_clr_loop pbos_pre size_pre (size - 1 ) initial )
  **  (R )
.

Definition OS_TaskStkClr_return_wit_1 := 
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) (PreH7 : ((Z.land opt_pre 1) <> 0)) (PreH8 : ((Z.land opt_pre 2) <> 0)) (PreH9 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (task_stk_clr_loop pbos_pre size_pre size initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
) \/
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) (PreH7 : ((Z.land opt_pre 1) <> 0)) (PreH8 : ((Z.land opt_pre 2) <> 0)) (PreH9 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (task_stk_clr_loop pbos_pre size_pre size initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
).

Definition OS_TaskStkClr_return_wit_1_split_goal_spatial := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) (PreH7 : ((Z.land opt_pre 1) <> 0)) (PreH8 : ((Z.land opt_pre 2) <> 0)) (PreH9 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (task_stk_clr_loop pbos_pre size_pre size initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
.

Definition OS_TaskStkClr_return_wit_2 := 
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 2) = 0)) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : (0 <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
) \/
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 2) = 0)) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : (0 <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
).

Definition OS_TaskStkClr_return_wit_2_split_goal_spatial := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 2) = 0)) (PreH2 : ((Z.land opt_pre 1) <> 0)) (PreH3 : (0 <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
.

Definition OS_TaskStkClr_return_wit_3 := 
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : (0 <= size_pre)) (PreH3 : (size_pre <= UINT_MAX)) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
) \/
(
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : (0 <= size_pre)) (PreH3 : (size_pre <= UINT_MAX)) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
).

Definition OS_TaskStkClr_return_wit_3_split_goal_spatial := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (PreH1 : ((Z.land opt_pre 1) = 0)) (PreH2 : (0 <= size_pre)) (PreH3 : (size_pre <= UINT_MAX)) (PreH4 : (0 <= opt_pre)) (PreH5 : (opt_pre <= 65535)) ,
  (task_stk_clr_pre pbos_pre size_pre opt_pre initial )
  **  (R )
|--
  (task_stk_clr_post pbos_pre size_pre opt_pre initial )
  **  (R )
.

Definition OS_TaskStkClr_partial_solve_wit_1_pure := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) (PreH7 : ((Z.land opt_pre 1) <> 0)) (PreH8 : ((Z.land opt_pre 2) <> 0)) (PreH9 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  ((( &( "size" ) )) # UInt  |-> size)
  **  ((( &( "opt" ) )) # UShort  |-> opt_pre)
  **  ((( &( "pbos" ) )) # Ptr  |-> pbos)
  **  (task_stk_clr_loop pbos_pre size_pre size initial )
  **  (R )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ ((pbos_pre + ((size_pre - size ) * sizeof(UINT))) = (pbos_pre + ((size_pre - size ) * sizeof(UINT)))) ”
.

Definition OS_TaskStkClr_partial_solve_wit_1_aux := 
forall (opt_pre: Z) (size_pre: Z) (pbos_pre: Z) (R: Assertion) (initial: (@list (@option Z))) (pbos: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= UINT_MAX)) (PreH5 : (0 <= opt_pre)) (PreH6 : (opt_pre <= 65535)) (PreH7 : ((Z.land opt_pre 1) <> 0)) (PreH8 : ((Z.land opt_pre 2) <> 0)) (PreH9 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  ((( &( "pbos" ) )) # Ptr  |-> pbos)
  **  (task_stk_clr_loop pbos_pre size_pre size initial )
  **  (R )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ ((pbos_pre + ((size_pre - size ) * sizeof(UINT))) = (pbos_pre + ((size_pre - size ) * sizeof(UINT)))) ” 
  &&  “ (size > 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= UINT_MAX) ” 
  &&  “ (0 <= opt_pre) ” 
  &&  “ (opt_pre <= 65535) ” 
  &&  “ ((Z.land opt_pre 1) <> 0) ” 
  &&  “ ((Z.land opt_pre 2) <> 0) ” 
  &&  “ (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT)))) ”
  &&  ((( &( "pbos" ) )) # Ptr  |-> (pbos_pre + ((size_pre - size ) * sizeof(UINT))))
  **  (task_stk_clr_loop pbos_pre size_pre size initial )
  **  (R )
.

Definition OS_TaskStkClr_partial_solve_wit_1 := OS_TaskStkClr_partial_solve_wit_1_pure -> OS_TaskStkClr_partial_solve_wit_1_aux.

Definition OS_TaskStkClr_which_implies_wit_1 := 
(
forall (size_pre: Z) (pbos_pre: Z) (initial: (@list (@option Z))) (size: Z) (pbos: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (task_stk_clr_loop pbos_pre size_pre size initial )
|--
  “ ((Zlength (initial)) = size_pre) ” 
  &&  “ (0 < pbos_pre) ” 
  &&  “ ((pbos_pre % ( 4 ) ) = 0) ” 
  &&  “ ((pbos_pre + (size_pre * sizeof(UINT))) <= UINT_MAX) ” 
  &&  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT)))) ” 
  &&  “ (0 < pbos) ” 
  &&  “ ((pbos + (1 * sizeof(UINT))) <= UINT_MAX) ”
  &&  ((pbos) # UInt  |->_)
  **  (task_stk_clr_residual pbos_pre size_pre size initial )
) \/
(
forall (size_pre: Z) (pbos_pre: Z) (initial: (@list (@option Z))) (size: Z) (pbos: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT))))) ,
  (task_stk_clr_loop pbos_pre size_pre size initial )
|--
  EX (x: Z) ,
  “ ((Zlength (initial)) = size_pre) ” 
  &&  “ (0 < pbos_pre) ” 
  &&  “ ((pbos_pre % ( 4 ) ) = 0) ” 
  &&  “ ((pbos_pre + (size_pre * sizeof(UINT))) <= UINT_MAX) ” 
  &&  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (pbos = (pbos_pre + ((size_pre - size ) * sizeof(UINT)))) ” 
  &&  “ (0 < pbos) ” 
  &&  “ ((pbos + (1 * sizeof(UINT))) <= UINT_MAX) ”
  &&  ((pbos) # UInt  |-> x)
  **  (task_stk_clr_residual pbos_pre size_pre size initial )
).

Module Type VC_Correct.


Axiom proof_of_OS_TaskStkClr_safety_wit_1 : OS_TaskStkClr_safety_wit_1.
Axiom proof_of_OS_TaskStkClr_entail_wit_1 : OS_TaskStkClr_entail_wit_1.
Axiom proof_of_OS_TaskStkClr_entail_wit_2 : OS_TaskStkClr_entail_wit_2.
Axiom proof_of_OS_TaskStkClr_return_wit_1 : OS_TaskStkClr_return_wit_1.
Axiom proof_of_OS_TaskStkClr_return_wit_2 : OS_TaskStkClr_return_wit_2.
Axiom proof_of_OS_TaskStkClr_return_wit_3 : OS_TaskStkClr_return_wit_3.
Axiom proof_of_OS_TaskStkClr_partial_solve_wit_1_pure : OS_TaskStkClr_partial_solve_wit_1_pure.
Axiom proof_of_OS_TaskStkClr_partial_solve_wit_1 : OS_TaskStkClr_partial_solve_wit_1.
Axiom proof_of_OS_TaskStkClr_which_implies_wit_1 : OS_TaskStkClr_which_implies_wit_1.

End VC_Correct.
