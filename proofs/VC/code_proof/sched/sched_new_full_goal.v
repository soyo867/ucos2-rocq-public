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
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_SchedNew -----*)

Definition OS_SchedNew_safety_wit_1 := 
(
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) )) ”
) \/
(
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) )) ”
).

Definition OS_SchedNew_safety_wit_1_split_goal_1 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) ) <= INT_MAX) ”
.

Definition OS_SchedNew_safety_wit_1_split_goal_2 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ ((INT_MIN) <= ((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) )) ”
.

Definition OS_SchedNew_safety_wit_2 := 
(
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ ((signed_last_nbits ((y * (2^3) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((y * (2^3) )) (32))) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
) \/
(
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ ((signed_last_nbits ((y * (2^3) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((y * (2^3) )) (32))) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
).

Definition OS_SchedNew_safety_wit_2_split_goal_1 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ ((signed_last_nbits ((y * (2^3) )) (32)) <= INT_MAX) ”
.

Definition OS_SchedNew_safety_wit_2_split_goal_2 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((y * (2^3) )) (32))) ”
.

Definition OS_SchedNew_safety_wit_2_split_goal_3 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (3 <= 31) ”
.

Definition OS_SchedNew_safety_wit_2_split_goal_4 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (0 <= 3) ”
.

Definition OS_SchedNew_entail_wit_1 := 
(
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ ((Znth group unmap_table 0) = (unmap_value (group))) ” 
  &&  “ (0 <= (Znth group unmap_table 0)) ” 
  &&  “ ((Znth group unmap_table 0) < 8) ” 
  &&  “ (0 <= (Znth ((Znth group unmap_table 0)) (rows) (0))) ” 
  &&  “ ((Znth ((Znth group unmap_table 0)) (rows) (0)) < 256) ” 
  &&  “ (0 <= (unmap_value ((Znth ((Znth group unmap_table 0)) (rows) (0))))) ” 
  &&  “ ((unmap_value ((Znth ((Znth group unmap_table 0)) (rows) (0)))) < 8) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
) \/
(
forall (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  TT && emp 
|--
  “ ((unmap_value ((Znth ((Znth group unmap_table 0)) (rows) (0)))) < 8) ” 
  &&  “ (0 <= (unmap_value ((Znth ((Znth group unmap_table 0)) (rows) (0))))) ” 
  &&  “ ((Znth ((Znth group unmap_table 0)) (rows) (0)) < 256) ” 
  &&  “ (0 <= (Znth ((Znth group unmap_table 0)) (rows) (0))) ” 
  &&  “ ((Znth group unmap_table 0) < 8) ” 
  &&  “ (0 <= (Znth group unmap_table 0)) ” 
  &&  “ ((Znth group unmap_table 0) = (unmap_value (group))) ”
  &&  emp
).

Definition OS_SchedNew_entail_wit_1_split_goal_1 := 
forall (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  ((unmap_value ((Znth ((Znth group unmap_table 0)) (rows) (0)))) < 8)
.

Definition OS_SchedNew_entail_wit_1_split_goal_2 := 
forall (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (0 <= (unmap_value ((Znth ((Znth group unmap_table 0)) (rows) (0)))))
.

Definition OS_SchedNew_entail_wit_1_split_goal_3 := 
forall (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  ((Znth ((Znth group unmap_table 0)) (rows) (0)) < 256)
.

Definition OS_SchedNew_entail_wit_1_split_goal_4 := 
forall (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (0 <= (Znth ((Znth group unmap_table 0)) (rows) (0)))
.

Definition OS_SchedNew_entail_wit_1_split_goal_5 := 
forall (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  ((Znth group unmap_table 0) < 8)
.

Definition OS_SchedNew_entail_wit_1_split_goal_6 := 
forall (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (0 <= (Znth group unmap_table 0))
.

Definition OS_SchedNew_entail_wit_1_split_goal_7 := 
forall (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  ((Znth group unmap_table 0) = (unmap_value (group)))
.

Definition OS_SchedNew_return_wit_1 := 
(
forall (frame: Assertion) (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (unsigned_last_nbits (((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) )) (8)))
  **  (frame )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
  &&  (sched_new_rep sg group rows (sched_new_priority (group) (rows)) )
  **  (frame )
) \/
(
forall (frame: Assertion) (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (unsigned_last_nbits (((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) )) (8)))
  **  (frame )
|--
  (sched_new_rep sg group rows (sched_new_priority (group) (rows)) )
  **  (frame )
).

Definition OS_SchedNew_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (rows: (@list Z)) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (unsigned_last_nbits (((signed_last_nbits ((Z.shiftl y 3)) (32)) + (Znth (Znth y rows 0) unmap_table 0) )) (8)))
  **  (frame )
|--
  (sched_new_rep sg group rows (sched_new_priority (group) (rows)) )
  **  (frame )
.

Definition OS_SchedNew_partial_solve_wit_1_pure := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  ((( &( "y" ) )) # UChar  |->_)
  **  (sched_new_rep sg group rows high )
  **  (frame )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
.

Definition OS_SchedNew_partial_solve_wit_1_aux := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
  **  (frame )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
  &&  (sched_new_rep sg group rows high )
  **  (frame )
.

Definition OS_SchedNew_partial_solve_wit_1 := OS_SchedNew_partial_solve_wit_1_pure -> OS_SchedNew_partial_solve_wit_1_aux.

Definition OS_SchedNew_partial_solve_wit_2 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= (unmap_value (group)))) (PreH5 : ((unmap_value (group)) < 8)) (PreH6 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (unmap_value (group))) ” 
  &&  “ ((unmap_value (group)) < 8) ” 
  &&  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
  &&  (((( &( "OSUnMapTbl" ) ) + (group * sizeof(UCHAR)))) # UChar  |-> (Znth group unmap_table 0))
  **  (UCharArray.missing_i ( &( "OSUnMapTbl" ) ) group 0 256 unmap_table )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
.

Definition OS_SchedNew_partial_solve_wit_3 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (y = (unmap_value (group))) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < 8) ” 
  &&  “ (0 <= (Znth (y) (rows) (0))) ” 
  &&  “ ((Znth (y) (rows) (0)) < 256) ” 
  &&  “ (0 <= (unmap_value ((Znth (y) (rows) (0))))) ” 
  &&  “ ((unmap_value ((Znth (y) (rows) (0)))) < 8) ”
  &&  (((( &( "OSRdyTbl" ) ) + (y * sizeof(UCHAR)))) # UChar  |-> (Znth y rows 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) y 0 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
.

Definition OS_SchedNew_partial_solve_wit_4 := 
forall (frame: Assertion) (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (y: Z) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (y = (unmap_value (group)))) (PreH3 : (0 <= y)) (PreH4 : (y < 8)) (PreH5 : (0 <= (Znth (y) (rows) (0)))) (PreH6 : ((Znth (y) (rows) (0)) < 256)) (PreH7 : (0 <= (unmap_value ((Znth (y) (rows) (0)))))) (PreH8 : ((unmap_value ((Znth (y) (rows) (0)))) < 8)) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (y = (unmap_value (group))) ” 
  &&  “ (0 <= y) ” 
  &&  “ (y < 8) ” 
  &&  “ (0 <= (Znth (y) (rows) (0))) ” 
  &&  “ ((Znth (y) (rows) (0)) < 256) ” 
  &&  “ (0 <= (unmap_value ((Znth (y) (rows) (0))))) ” 
  &&  “ ((unmap_value ((Znth (y) (rows) (0)))) < 8) ”
  &&  (((( &( "OSUnMapTbl" ) ) + ((Znth y rows 0) * sizeof(UCHAR)))) # UChar  |-> (Znth (Znth y rows 0) unmap_table 0))
  **  (UCharArray.missing_i ( &( "OSUnMapTbl" ) ) (Znth y rows 0) 0 256 unmap_table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
  **  (frame )
.

Definition OS_SchedNew_which_implies_wit_1 := 
(
forall (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
|--
  “ (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= (unmap_value (group))) ” 
  &&  “ ((unmap_value (group)) < 8) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
) \/
(
forall (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
|--
  “ ((unmap_value (group)) < 8) ” 
  &&  “ (0 <= (unmap_value (group))) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= group) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
).

Definition OS_SchedNew_which_implies_wit_1_split_goal_1 := 
forall (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
|--
  “ ((unmap_value (group)) < 8) ”
.

Definition OS_SchedNew_which_implies_wit_1_split_goal_2 := 
forall (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
|--
  “ (0 <= (unmap_value (group))) ”
.

Definition OS_SchedNew_which_implies_wit_1_split_goal_3 := 
forall (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
|--
  “ (group < 256) ”
.

Definition OS_SchedNew_which_implies_wit_1_split_goal_4 := 
forall (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
|--
  “ (0 <= group) ”
.

Definition OS_SchedNew_which_implies_wit_1_split_goal_spatial := 
forall (rows: (@list Z)) (high: Z) (group: Z) (sg: StableGlobVars) (PreH1 : (sched_new_global_addresses sg ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) ,
  (sched_new_rep sg group rows high )
|--
  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  (UCharArray.full ( &( "OSUnMapTbl" ) ) 256 unmap_table )
  **  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> high)
.

Module Type VC_Correct.


Axiom proof_of_OS_SchedNew_safety_wit_1 : OS_SchedNew_safety_wit_1.
Axiom proof_of_OS_SchedNew_safety_wit_2 : OS_SchedNew_safety_wit_2.
Axiom proof_of_OS_SchedNew_entail_wit_1 : OS_SchedNew_entail_wit_1.
Axiom proof_of_OS_SchedNew_return_wit_1 : OS_SchedNew_return_wit_1.
Axiom proof_of_OS_SchedNew_partial_solve_wit_1_pure : OS_SchedNew_partial_solve_wit_1_pure.
Axiom proof_of_OS_SchedNew_partial_solve_wit_1 : OS_SchedNew_partial_solve_wit_1.
Axiom proof_of_OS_SchedNew_partial_solve_wit_2 : OS_SchedNew_partial_solve_wit_2.
Axiom proof_of_OS_SchedNew_partial_solve_wit_3 : OS_SchedNew_partial_solve_wit_3.
Axiom proof_of_OS_SchedNew_partial_solve_wit_4 : OS_SchedNew_partial_solve_wit_4.
Axiom proof_of_OS_SchedNew_which_implies_wit_1 : OS_SchedNew_which_implies_wit_1.

End VC_Correct.
