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
Require Import Ucos2Verify.VC.code.core.spec.os_version_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OSVersion -----*)

Definition OSVersion_return_wit_1 := 
(
forall (frame: Assertion) (X: (Z -> (UCOS2_Verify_State -> Prop))) (s: UCOS2_Verify_State) (PreH1 : (os_version_safe s X )) ,
  (frame )
|--
  “ (29300 = 29300) ” 
  &&  “ (os_version_safe_return s 29300 X ) ”
  &&  (frame )
) \/
(
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (s: UCOS2_Verify_State) (PreH1 : (os_version_safe s X )) ,
  TT && emp 
|--
  “ (os_version_safe_return s 29300 X ) ”
  &&  emp
).

Definition OSVersion_return_wit_1_split_goal_1 := 
forall (X: (Z -> (UCOS2_Verify_State -> Prop))) (s: UCOS2_Verify_State) (PreH1 : (os_version_safe s X )) ,
  (os_version_safe_return s 29300 X )
.

Module Type VC_Correct.


Axiom proof_of_OSVersion_return_wit_1 : OSVersion_return_wit_1.

End VC_Correct.
