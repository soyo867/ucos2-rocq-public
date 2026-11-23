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
From Ucos2Verify.VC.code.task Require Import task_reg_get_id_goal.
From Ucos2Verify.VC.code.task Require Import task_reg_get_id_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_reg_get_id_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskRegGetID_entail_wit_1 : OSTaskRegGetID_entail_wit_1.
Proof.
  left; intros.
  sep_apply (critical_region_interval_open_invariant
    critical sg invocation before entry_2 PreH1 PreH3).
  sep_apply (task_reg_get_id_split sg entry_2).
  Intros.
  Exists entry_2.
  unfold task_reg_get_id_addresses in PreH5.
  rewrite PreH5.
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGetID_entail_wit_2 : OSTaskRegGetID_entail_wit_2.
Proof.
  left; intros.
  Exists entry_2.
  pose proof (task_reg_get_id_effect_exhausted
    sg entry_2 PreH3 ltac:(lia)) as Heffect.
  pose proof (task_reg_get_id_merge_updated sg entry_2
    (task_reg_get_id_next entry_2) PreH3 (conj PreH7 PreH8)) as Hmerge.
  rewrite task_reg_get_id_update_put_back in Hmerge.
  unfold task_reg_get_id_addresses in PreH4.
  rewrite <- PreH4.
  sep_apply Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGetID_entail_wit_3 : OSTaskRegGetID_entail_wit_3.
Proof.
  left; intros.
  Exists entry.
  pose proof (task_reg_get_id_effect_available sg entry PreH3 PreH1) as Heffect.
  unfold task_reg_get_id_addresses in PreH4.
  rewrite <- PreH4.
  sep_apply (task_reg_get_id_merge_updated sg entry
    (task_reg_get_id_next entry + 1) PreH3 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGetID_return_wit_1 : OSTaskRegGetID_return_wit_1.
Proof.
  left; intros.
  unfold task_reg_get_id_restore_post.
  Intros current.
  assert (Hexec : safeExec (eq current) (StateRelMonad.ret (id, 0))
    (fun result state => X (fst result) (snd result) state)).
  { eapply (task_reg_get_id_safe_return critical sg invocation before entry
      (task_reg_get_id_update entry (task_reg_get_id_next entry + 1))
      current id 0 X); eauto; tauto. }
  unfold task_reg_get_id_post.
  Exists entry (task_reg_get_id_update entry (task_reg_get_id_next entry + 1))
    current 0.
  unfold interrupt_saved_value in PreH3.
  destruct PreH3 as [_ Hmask].
  rewrite Hmask.
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGetID_return_wit_2 : OSTaskRegGetID_return_wit_2.
Proof.
  left; intros.
  unfold task_reg_get_id_restore_post.
  Intros current.
  assert (Hexec : safeExec (eq current) (StateRelMonad.ret (1, 150))
    (fun result state => X (fst result) (snd result) state)).
  { eapply (task_reg_get_id_safe_return critical sg invocation before entry
      entry current 1 150 X); eauto; tauto. }
  unfold task_reg_get_id_post.
  Exists entry entry current 150.
  unfold interrupt_saved_value in PreH3.
  destruct PreH3 as [_ Hmask].
  rewrite Hmask.
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGetID_which_implies_wit_1 : OSTaskRegGetID_which_implies_wit_1.
Proof.
  left; intros.
  unfold task_reg_get_id_pre, task_reg_get_id_closed.
  entailer!.
Qed.

