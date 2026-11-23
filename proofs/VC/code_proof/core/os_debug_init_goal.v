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
Require Import Ucos2Verify.VC.code.core.spec.os_debug_init_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSDebugInit -----*)

Definition OSDebugInit_safety_wit_1 := 
forall (frame: Assertion) ,
  ((( &( "ptemp" ) )) # Ptr  |-> ( &( "OSTimeTickHookEn" ) ))
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSDebugInit_safety_wit_2 := 
forall (frame: Assertion) ,
  ((( &( "ptemp" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSDebugInit_return_wit_1 := 
forall (frame: Assertion) ,
  (frame )
|--
  (frame )
.

Module Type VC_Correct.


Axiom proof_of_OSDebugInit_safety_wit_1 : OSDebugInit_safety_wit_1.
Axiom proof_of_OSDebugInit_safety_wit_2 : OSDebugInit_safety_wit_2.
Axiom proof_of_OSDebugInit_return_wit_1 : OSDebugInit_return_wit_1.

End VC_Correct.
