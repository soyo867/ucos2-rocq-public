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
From Ucos2Verify.VC.code.timer Require Import tmr_signal_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_signal_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_signal_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSTmrSignal_return_wit_1 : OSTmrSignal_return_wit_1.
Proof.
  unfold OSTmrSignal_return_wit_1; left; intros.
  unfold tmr_signal_post; entailer!.
Qed. 

Lemma proof_of_OSTmrSignal_which_implies_wit_1 : OSTmrSignal_which_implies_wit_1.
Proof.
  unfold OSTmrSignal_which_implies_wit_1; left.
  intros X eid before mask caller sg critical saved_local environment
    [Htimer Hprofile] Hvalid Haddress Hsafe.
  pose proof (tmr_signal_safe_sem_post environment critical sg caller mask
    eid before X Hsafe) as Hcallee_safe.
  rewrite (tmr_signal_closed_split_signal environment critical saved_local
    sg caller mask before Htimer Hvalid).
  rewrite Haddress; entailer!.
Qed. 

Lemma proof_of_OSSemPost_derive_tmr_signal_sem_post_by_sem_post_api : OSSemPost_derive_tmr_signal_sem_post_by_sem_post_api.
Proof.
  unfold OSSemPost_derive_tmr_signal_sem_post_by_sem_post_api.
  intros pe X observed eid before mask caller sg critical saved_local environment.
  Intros.
  match goal with
  | H : tmr_signal_profile sg |- _ => destruct H as [Htimer Hprofile]
  end.
  Exists environment saved_local critical sg caller mask before eid observed
    (tmr_signal_pointer before) X.
  match goal with
  | Hvalid : UCOS2_state_inv sg before,
    Haddress : ?address = g_OSTmrSemSignal sg |- _ =>
      pose proof (tmr_signal_closed_split_signal environment critical saved_local
        sg caller mask before Htimer Hvalid) as Hread;
      rewrite <- Haddress in Hread;
      rewrite <- Hread
  end.
  apply derivable1s_emp_sepcon_unfold.
  - match goal with
    | H : tmr_signal_optional_event_layout sg _ eid |- _ =>
        destruct H as [Hnull | Hlayout]
    end.
    + Right; entailer!.
    + Left; entailer!.
  - apply derivable1s_wand_sepcon_adjoint; entailer!.
Qed. 

