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
From Ucos2Verify.VC.code.core Require Import os_version_goal.
From Ucos2Verify.VC.code.core Require Import os_version_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.os_version_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSVersion_return_wit_1 : OSVersion_return_wit_1.
Proof.
  unfold OSVersion_return_wit_1.
  left.
  intros frame X s Hsafe.
  pose proof (os_version_safe_return_same_state UCOS2_Verify_State s X Hsafe)
    as Hreturn.
  entailer!.
Qed.

