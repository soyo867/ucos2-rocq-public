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
From Ucos2Verify.VC.code.time Require Import time_set_goal.
From Ucos2Verify.VC.code.time Require Import time_set_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.time.spec.time_set_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSTimeSet_return_wit_1 : OSTimeSet_return_wit_1.
Proof.
  left; intros.
  pose proof (time_set_restored_return critical sg invocation before entry_3
    checkpoint requested after_2 PreH2 PreH1) as Hpost.
  pose proof (time_set_safe_return critical sg invocation before requested
    after_2 X Hpost PreH15) as Hsafe.
  Exists after_2; entailer!.
Qed. 

Lemma proof_of_OSTimeSet_which_implies_wit_1 : OSTimeSet_which_implies_wit_1.
Proof.
  left; intros.
  rewrite (time_set_inv_split_clock platform critical sg invocation origin mask
    cpu_sr before entry_2 PreH2 PreH3 PreH4).
  Exists entry_2; rewrite PreH1; entailer!.
Qed. 

Lemma proof_of_OSTimeSet_which_implies_wit_2 : OSTimeSet_which_implies_wit_2.
Proof.
  left; intros.
  assert (Hticks : 0 <= requested < 4294967296).
  { change (requested <= 4294967295) in PreH3; lia. }
  Exists entry_2 (time_set_state entry_2 requested).
  rewrite PreH1.
  sep_apply_l_atomic (time_set_store_frame_merge_updated platform critical sg
    invocation origin mask cpu_sr before entry_2 requested Hticks).
  entailer!.
Qed. 

