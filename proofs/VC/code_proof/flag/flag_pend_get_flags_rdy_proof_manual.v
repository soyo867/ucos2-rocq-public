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
From Ucos2Verify.VC.code.flag Require Import flag_pend_get_flags_rdy_goal.
From Ucos2Verify.VC.code.flag Require Import flag_pend_get_flags_rdy_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_get_flags_rdy_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSFlagPendGetFlagsRdy_return_wit_1 : OSFlagPendGetFlagsRdy_return_wit_1.
Proof.
  unfold OSFlagPendGetFlagsRdy_return_wit_1; left; intros.
  eapply flag_pend_get_flags_rdy_restore_api_post; eassumption.
Qed. 

Lemma proof_of_OSFlagPendGetFlagsRdy_which_implies_wit_1 : OSFlagPendGetFlagsRdy_which_implies_wit_1.
Proof.
  unfold OSFlagPendGetFlagsRdy_which_implies_wit_1; left; intros.
  pose proof PreH3 as [Hinterval [Hvalid Hsaved]].
  destruct (PreH2 entry_2 Hinterval Hvalid) as [snapshot Hobserved].
  pose proof Hobserved as [Hnonnull [residual Hview]].
  pose proof (flag_pend_get_flags_rdy_read_split sg entry_2 caller
    snapshot residual Hview) as Hsplit.
  rewrite <- PreH1 in Hsplit.
  cbn [tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  Intros.
  prop_apply_p (UCOS2_C_Rules.store_ushort_range
    (tcb_field_address (task_reg_get_current_pointer sg entry_2) TCBFlagsRdy)
    snapshot).
  Intros.
  Exists residual snapshot entry_2.
  entailer!.
Qed. 

Lemma proof_of_OSFlagPendGetFlagsRdy_which_implies_wit_2 : OSFlagPendGetFlagsRdy_which_implies_wit_2.
Proof.
  unfold OSFlagPendGetFlagsRdy_which_implies_wit_2; left; intros.
  pose proof PreH2 as [Hinterval [Hvalid Hsaved]].
  pose proof (flag_pend_get_flags_rdy_read_merge sg entry caller snapshot
    residual Hvalid PreH3) as Hmerge.
  rewrite <- PreH1 in Hmerge.
  cbn [tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed. 

