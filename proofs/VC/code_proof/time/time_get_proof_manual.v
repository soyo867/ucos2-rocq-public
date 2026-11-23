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
From Ucos2Verify.VC.code.time Require Import time_get_goal.
From Ucos2Verify.VC.code.time Require Import time_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.time.spec.time_get_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSTimeGet_return_wit_1 : OSTimeGet_return_wit_1.
Proof.
  unfold OSTimeGet_return_wit_1; left; intros.
  sep_apply (time_get_restore_api_post platform critical sg invocation origin
    mask retval before entry X PreH2 PreH7).
  entailer!.
Qed.

Lemma proof_of_OSTimeGet_which_implies_wit_1 : OSTimeGet_which_implies_wit_1.
Proof.
  unfold OSTimeGet_which_implies_wit_1; left; intros.
  Exists entry_2.
  sep_apply (time_get_read_split sg entry_2).
  rewrite PreH1.
  entailer!.
Qed.

Lemma proof_of_OSTimeGet_which_implies_wit_2 : OSTimeGet_which_implies_wit_2.
Proof.
  unfold OSTimeGet_which_implies_wit_2; left; intros.
  rewrite PreH1.
  apply time_get_read_merge.
Qed.

