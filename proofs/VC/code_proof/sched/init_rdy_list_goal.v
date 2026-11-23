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
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OS_InitRdyList -----*)

Definition OS_InitRdyList_safety_wit_1 := 
forall (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition OS_InitRdyList_safety_wit_2 := 
forall (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitRdyList_safety_wit_3 := 
forall (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitRdyList_entail_wit_1 := 
  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) 0 )
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) 0 )
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
.

Definition OS_InitRdyList_entail_wit_2 := 
forall (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) (i + 1 ) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) (i + 1 ) )
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
.

Definition OS_InitRdyList_return_wit_1 := 
(
forall (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> 0)
|--
  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
) \/
(
forall (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> 0)
|--
  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
).

Definition OS_InitRdyList_return_wit_1_split_goal_spatial := 
forall (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> 0)
|--
  (init_rdy_list_post ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
.

Definition OS_InitRdyList_partial_solve_wit_1 := 
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
|--
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
.

Definition OS_InitRdyList_partial_solve_wit_2_pure := 
forall (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ”
.

Definition OS_InitRdyList_partial_solve_wit_2_aux := 
forall (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ”
  &&  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
.

Definition OS_InitRdyList_partial_solve_wit_2 := OS_InitRdyList_partial_solve_wit_2_pure -> OS_InitRdyList_partial_solve_wit_2_aux.

Definition OS_InitRdyList_partial_solve_wit_3_pure := 
forall (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ”
.

Definition OS_InitRdyList_partial_solve_wit_3_aux := 
forall (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ”
  &&  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> 0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
.

Definition OS_InitRdyList_partial_solve_wit_3 := OS_InitRdyList_partial_solve_wit_3_pure -> OS_InitRdyList_partial_solve_wit_3_aux.

Definition OS_InitRdyList_which_implies_wit_1 := 
(
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
|--
  ((( &( "OSRdyGrp" ) )) # UChar  |->_)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) 0 )
  **  ((( &( "OSPrioCur" ) )) # UChar  |->_)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |->_)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |->_)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |->_)
) \/
(
  (init_rdy_list_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioCur" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBCur" ) ) )
|--
  EX (x_5: Z)  (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> x_5)
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> x_4)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> x_3)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> x_2)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> x)
  **  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) 0 )
).

Definition OS_InitRdyList_which_implies_wit_2 := 
(
forall (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
|--
  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |->_)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
) \/
(
forall (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) i )
|--
  EX (x: Z) ,
  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> x)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
).

Definition OS_InitRdyList_which_implies_wit_3 := 
(
forall (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
|--
  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) (i + 1 ) )
) \/
(
forall (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
|--
  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) (i + 1 ) )
).

Definition OS_InitRdyList_which_implies_wit_3_split_goal_spatial := 
forall (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (((( &( "OSRdyTbl" ) ) + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (init_rdy_list_row_frame ( &( "OSRdyTbl" ) ) i )
|--
  (init_rdy_list_table_prefix ( &( "OSRdyTbl" ) ) (i + 1 ) )
.

Module Type VC_Correct.


Axiom proof_of_OS_InitRdyList_safety_wit_1 : OS_InitRdyList_safety_wit_1.
Axiom proof_of_OS_InitRdyList_safety_wit_2 : OS_InitRdyList_safety_wit_2.
Axiom proof_of_OS_InitRdyList_safety_wit_3 : OS_InitRdyList_safety_wit_3.
Axiom proof_of_OS_InitRdyList_entail_wit_1 : OS_InitRdyList_entail_wit_1.
Axiom proof_of_OS_InitRdyList_entail_wit_2 : OS_InitRdyList_entail_wit_2.
Axiom proof_of_OS_InitRdyList_return_wit_1 : OS_InitRdyList_return_wit_1.
Axiom proof_of_OS_InitRdyList_partial_solve_wit_1 : OS_InitRdyList_partial_solve_wit_1.
Axiom proof_of_OS_InitRdyList_partial_solve_wit_2_pure : OS_InitRdyList_partial_solve_wit_2_pure.
Axiom proof_of_OS_InitRdyList_partial_solve_wit_2 : OS_InitRdyList_partial_solve_wit_2.
Axiom proof_of_OS_InitRdyList_partial_solve_wit_3_pure : OS_InitRdyList_partial_solve_wit_3_pure.
Axiom proof_of_OS_InitRdyList_partial_solve_wit_3 : OS_InitRdyList_partial_solve_wit_3.
Axiom proof_of_OS_InitRdyList_which_implies_wit_1 : OS_InitRdyList_which_implies_wit_1.
Axiom proof_of_OS_InitRdyList_which_implies_wit_2 : OS_InitRdyList_which_implies_wit_2.
Axiom proof_of_OS_InitRdyList_which_implies_wit_3 : OS_InitRdyList_which_implies_wit_3.

End VC_Correct.
