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
From Ucos2Verify.VC.code.task Require Import task_name_set_continuation_goal.
From Ucos2Verify.VC.code.task Require Import task_name_set_continuation_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_name_set_continuation_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.


Require Import Ucos2Verify.VC.code.task.spec.task_name_set_continuation_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTaskNameSet_entail_wit_1_1 : OSTaskNameSet_entail_wit_1_1.
Proof.
left; intros; subst perr_pre pname_pre prio_pre; Intros.
  match goal with H : UCOS2_state_inv sg before |- _ => rename H into Hvalid end.
  match goal with H : task_name_set_continuation_admission _ _ _ _ _ |- _ => rename H into Hadmit end.
  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  assert (Hpriority : task_name_set_valid_priority request) by (unfold task_name_set_valid_priority; lia).
  sep_apply_l_atomic (task_name_set_continuation_save_call_open environment critical saved_local sg
    call mask retval before request name Hvalid Hadmit Hpriority ltac:(lia) ltac:(lia)).
  Intros active acquired.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [Hsame _]]]]]]].
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold task_name_set_continuation_masked, UCOS2_inv; Intros.
  rewrite Hinv, Horigin.
  Exists active acquired.
  unfold task_name_set_continuation_call_binding.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  subst; entailer!; try apply derivable1_truep_intros.
  repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_1_2 : OSTaskNameSet_entail_wit_1_2.
Proof.
left; intros; subst perr_pre pname_pre prio_pre; Intros.
  match goal with H : UCOS2_state_inv sg before |- _ => rename H into Hvalid end.
  match goal with H : task_name_set_continuation_admission _ _ _ _ _ |- _ => rename H into Hadmit end.
  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  assert (Hpriority : task_name_set_valid_priority request) by (unfold task_name_set_valid_priority; lia).
  sep_apply_l_atomic (task_name_set_continuation_save_call_open environment critical saved_local sg
    call mask retval before request name Hvalid Hadmit Hpriority ltac:(lia) ltac:(lia)).
  Intros active acquired.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [Hsame _]]]]]]].
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold task_name_set_continuation_masked, UCOS2_inv; Intros.
  rewrite Hinv, Horigin.
  Exists active acquired.
  unfold task_name_set_continuation_call_binding.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  subst; entailer!; try apply derivable1_truep_intros.
  repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_2 : OSTaskNameSet_entail_wit_2.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_addresses _ _ _ _ |- _ => rename H into Haddr end.
  match goal with H : task_name_set_layout _ |- _ => rename H into Hlayout end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [Hpriority [Hnonnull [Hnest [Hself [Hread [Hsave [Hsame [Hsaved Hvalid]]]]]]]].
  assert (Hrequest : request = 255).
  { rewrite IntLib.unsigned_last_nbits_eq in PreH1.
    - exact PreH1.
    - unfold task_name_set_valid_priority in Hpriority; destruct Hpriority; lia. }
  destruct (Hself Hrequest)
    as [tid [task Hcurrent]].
  pose proof (task_name_set_used_priority_in_range__g01_protected_name_store
    sg acquired tid task Hvalid (proj2 Hcurrent)) as Hrange.
  unfold UCOS2_inv; Intros.
  sep_apply_l_atomic (task_name_set_split_self sg acquired tid task Hcurrent).
  pose proof Haddr as [_ [Hcurrent_addr _]].
  rewrite <- Hcurrent_addr, (proj1 (Hlayout tid)).
  Exists tid task; entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_3 : OSTaskNameSet_entail_wit_3.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_addresses _ _ _ _ |- _ => rename H into Haddr end.
  match goal with H : task_name_set_layout _ |- _ => rename H into Hlayout end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  match goal with H : task_name_set_current _ _ _ |- _ => rename H into Hcurrent end.
  pose proof (proj1 Hcontext) as [Hpriority [Hnonnull [Hnest [Hself [Hread [Hsave [Hsame [Hsaved Hvalid]]]]]]]].
  pose proof Haddr as [_ [Hcurrent_addr _]].
  rewrite Hcurrent_addr, <- (proj1 (Hlayout tid)).
  rewrite Hcurrent_addr in Haddr.
  sep_apply_l_atomic (task_name_set_merge_self sg acquired tid task Hvalid Hcurrent).
  assert (Hresolved : task_name_set_resolved request acquired task.(curPrio)).
  { right; split; [assumption|exists tid, task; auto]. }
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_4_2 : OSTaskNameSet_entail_wit_4_2.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 (proj1 Hcontext)) as Hpriority.
  assert (Hnotself : request <> 255).
  { intro Hrequest; subst request; vm_compute in PreH1; congruence. }
  assert (Hrange : 0 <= request <= 63).
  { unfold task_name_set_valid_priority in Hpriority; tauto. }
  assert (Hresolved : task_name_set_resolved request acquired request).
  { left; auto. }
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_5 : OSTaskNameSet_entail_wit_5.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_addresses _ _ _ _ |- _ => rename H into Haddr end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [Hpriority [Hnonnull [Hnest [Hself [Hread [Hsave [Hsame [Hsaved Hvalid]]]]]]]].
  pose proof (proj1 Haddr) as Htable_addr.
  rewrite Htable_addr.
  rewrite Htable_addr in Haddr.
  sep_apply_l_atomic (task_name_set_merge_table sg acquired prio ltac:(lia) Hvalid).
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_6 : OSTaskNameSet_entail_wit_6.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_addresses _ _ _ _ |- _ => rename H into Haddr end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [Hpriority [Hnonnull [Hnest [Hself [Hread [Hsave [Hsame [Hsaved Hvalid]]]]]]]].
  assert (Hfree : acquired.(TskState).(prioTbl) prio = PTFree).
  { destruct (task_name_set_table_classify sg acquired prio _ _ _ Hvalid Haddr ltac:(lia))
      as [[Hentry Hfree]|[[Hentry Hreserved]|[tid [task [Htarget [Hentry Hpointer]]]]]];
      try assumption; exfalso; lia. }
  assert (Hstep : task_name_set_step prio name acquired 67 acquired)
    by (apply TaskNameSetFree; assumption).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &( "ptcb" ) ptcb).
  sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_7 : OSTaskNameSet_entail_wit_7.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_addresses _ _ _ _ |- _ => rename H into Haddr end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [Hpriority [Hnonnull [Hnest [Hself [Hread [Hsave [Hsame [Hsaved Hvalid]]]]]]]].
  assert (Hreserved : acquired.(TskState).(prioTbl) prio = PTReserved).
  { destruct (task_name_set_table_classify sg acquired prio _ _ _ Hvalid Haddr ltac:(lia))
      as [[Hentry Hfree]|[[Hentry Hreserved]|[tid [task [Htarget [Hentry Hpointer]]]]]];
      try assumption; exfalso; lia. }
  assert (Hstep : task_name_set_step prio name acquired 67 acquired)
    by (apply TaskNameSetReserved; assumption).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &( "ptcb" ) ptcb).
  sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_8 : OSTaskNameSet_entail_wit_8.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_addresses _ _ _ _ |- _ => rename H into Haddr end.
  match goal with H : task_name_set_layout _ |- _ => rename H into Hlayout end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [Hpriority [Hnonnull [Hnest [Hself [Hread [Hsave [Hsame [Hsaved Hvalid]]]]]]]].
  assert (Hselected : exists tid task,
    task_name_set_target acquired prio tid task /\ ptcb = task_slot_addr sg tid).
  { destruct (task_name_set_table_classify sg acquired prio _ _ _ Hvalid Haddr ltac:(lia))
      as [[Hentry Hfree]|[[Hentry Hreserved]|[tid [task [Htarget [Hentry Hpointer]]]]]];
      try (exfalso; lia).
    exists tid, task; split; [assumption|congruence]. }
  destruct Hselected as [tid [task [Htarget Hptcb]]].
  rewrite Hptcb; unfold UCOS2_inv; Intros.
  sep_apply_l_atomic (task_name_set_split_field sg acquired tid task (proj2 Htarget)).
  rewrite (proj2 (Hlayout tid)).
  Exists task tid; entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_entail_wit_9 : OSTaskNameSet_entail_wit_9.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_resolved _ _ _ |- _ => rename H into Hresolved end.
  match goal with H : task_name_set_layout _ |- _ => rename H into Hlayout end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  match goal with H : task_name_set_target _ _ _ _ |- _ => rename H into Htarget end.
  pose proof (proj1 Hcontext) as [Hpriority [Hnonnull [Hnest [Hself [Hread [Hsave [Hsame [Hsaved Hvalid]]]]]]]].
  destruct Hread as [chars Hreadable].
  subst ptcb; rewrite <- (proj2 (Hlayout tid)).
  sep_apply_l_atomic (task_name_set_merge_updated_field
    sg acquired tid task name chars Hvalid (proj2 Htarget) Hreadable).
  sep_apply_l_atomic (task_name_set_continuation_update_resources
    environment saved_local sg active acquired tid task name (proj2 Htarget)).
  assert (Hstep : task_name_set_step prio name acquired 0
    (task_name_set_update acquired tid task name))
    by (apply TaskNameSetStore; assumption).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &( "ptcb" ) (task_slot_addr sg tid)).
  sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists (task_name_set_update acquired tid task name); entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_1 : OSTaskNameSet_return_wit_1.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [_ [Hsaved _]]]]]]]].
  destruct Hsaved as [Hword Hmask].
  sep_apply_l_atomic (task_name_set_continuation_restore_call_open environment critical saved_local sg active cpu_sr acquired).
  Intros returned current.
  rewrite Hmask.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists returned 67 current.
  entailer!.
  eapply task_name_set_continuation_call_safe_return; [|eassumption].
  eapply task_name_set_continuation_call_context_result; eauto; tauto.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_2 : OSTaskNameSet_return_wit_2.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [_ [Hsaved _]]]]]]]].
  destruct Hsaved as [Hword Hmask].
  sep_apply_l_atomic (task_name_set_continuation_restore_call_open environment critical saved_local sg active cpu_sr acquired).
  Intros returned current.
  rewrite Hmask.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists returned 67 current.
  entailer!.
  eapply task_name_set_continuation_call_safe_return; [|eassumption].
  eapply task_name_set_continuation_call_context_result; eauto; tauto.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_3 : OSTaskNameSet_return_wit_3.
Proof.
left; intros; subst; Intros.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists call 18 before.

  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  rewrite task_name_set_continuation_closed_split.
  unfold task_name_set_closed.

  entailer!.
  apply task_name_set_continuation_call_safe_return; [|assumption].
  unfold task_name_set_continuation_call_result, task_name_set_valid_priority.
  right; right; left; repeat split; auto; lia.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_4 : OSTaskNameSet_return_wit_4.
Proof.
left; intros; subst; Intros.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists call 18 before.

  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  rewrite task_name_set_continuation_closed_split.
  unfold task_name_set_closed.

  entailer!.
  apply task_name_set_continuation_call_safe_return; [|assumption].
  unfold task_name_set_continuation_call_result, task_name_set_valid_priority.
  right; right; left; repeat split; auto; lia.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_5 : OSTaskNameSet_return_wit_5.
Proof.
left; intros; subst; Intros.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists call 12 before.

  entailer!.
  apply task_name_set_continuation_call_safe_return; [|assumption].
  unfold task_name_set_continuation_call_result, task_name_set_valid_priority.
  right; left; repeat split; auto; lia.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_6 : OSTaskNameSet_return_wit_6.
Proof.
left; intros; subst; Intros.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists call 12 before.

  entailer!.
  apply task_name_set_continuation_call_safe_return; [|assumption].
  unfold task_name_set_continuation_call_result, task_name_set_valid_priority.
  right; left; repeat split; auto; lia.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_7 : OSTaskNameSet_return_wit_7.
Proof.
left; intros; subst; Intros.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists call 42 before.

  entailer!.
  apply task_name_set_continuation_call_safe_return; [|assumption].
  unfold task_name_set_continuation_call_result, task_name_set_valid_priority.
  left; repeat split; auto; lia.
Qed.

Lemma proof_of_OSTaskNameSet_return_wit_8 : OSTaskNameSet_return_wit_8.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [_ [Hsaved _]]]]]]]].
  destruct Hsaved as [Hword Hmask].
  sep_apply_l_atomic (task_name_set_continuation_restore_call_open environment critical saved_local sg active cpu_sr released).
  Intros returned current.
  rewrite Hmask.
  repeat sep_apply_l_atomic (derivable1_truep_intros (TT ** TT)).
  Exists returned 0 current.
  entailer!.
  eapply task_name_set_continuation_call_safe_return; [|eassumption].
  eapply task_name_set_continuation_call_context_result; eauto; tauto.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_1 : OSTaskNameSet_which_implies_wit_1.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  rewrite task_name_set_continuation_closed_split.
  unfold task_name_set_closed, task_name_set_continuation_call_binding.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_2 : OSTaskNameSet_which_implies_wit_2.
Proof.
unfold OSTaskNameSet_which_implies_wit_2; left; intros; Intros.
  match goal with
  | H : task_name_set_addresses _ _ _ _ |- _ =>
      destruct H as [Htable [Hcurrent [Hnest Hbase]]]
  end.
  rewrite Hnest.
  sep_apply (task_name_set_observation_split critical sg invocation before).
  Intros.
  unfold task_name_set_addresses; entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_3 : OSTaskNameSet_which_implies_wit_3.
Proof.
unfold OSTaskNameSet_which_implies_wit_3; left; intros; Intros.
  match goal with
  | H : task_name_set_addresses _ _ _ _ |- _ =>
      destruct H as [Htable [Hcurrent [Hnest Hbase]]]
  end.
  rewrite Hnest.
  sep_apply (task_name_set_observation_merge critical sg invocation before).
  unfold task_name_set_addresses; entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_4 : OSTaskNameSet_which_implies_wit_4.
Proof.
unfold OSTaskNameSet_which_implies_wit_4; left; intros; Intros.
  match goal with
  | H : task_name_set_addresses _ _ _ _ |- _ =>
      destruct H as [Htable [Hcurrent [Hnest Hbase]]]
  end.
  rewrite Hnest.
  sep_apply (task_name_set_observation_merge critical sg invocation before).
  unfold task_name_set_addresses; entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_5 : OSTaskNameSet_which_implies_wit_5.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  rewrite task_name_set_continuation_closed_split.
  unfold task_name_set_closed, task_name_set_continuation_call_binding.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_6 : OSTaskNameSet_which_implies_wit_6.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_addresses _ _ _ _ |- _ => rename H into Haddr end.
  pose proof (proj1 Haddr) as Htable_addr.
  rewrite Htable_addr.
  rewrite Htable_addr in Haddr.
  sep_apply_l_atomic (task_name_set_split_table sg acquired prio ltac:(lia)).
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_7 : OSTaskNameSet_which_implies_wit_7.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [Hsame _]]]]]]].
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold task_name_set_continuation_masked, task_name_set_continuation_call_binding.
  rewrite Hinv, Horigin.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_8 : OSTaskNameSet_which_implies_wit_8.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [Hsame _]]]]]]].
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold task_name_set_continuation_masked, task_name_set_continuation_call_binding.
  rewrite Hinv, Horigin.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameSet_which_implies_wit_9 : OSTaskNameSet_which_implies_wit_9.
Proof.
left; intros; Intros.
  match goal with H : task_name_set_continuation_call_binding _ _ _ _ _ |- _ =>
    destruct H as [Hplatform [Hinv Horigin]]; subst platform invocation origin end.
  match goal with H : task_name_set_continuation_call_context _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcontext end.
  pose proof (proj1 Hcontext) as [_ [_ [_ [_ [_ [_ [Hsame _]]]]]]].
  destruct Hsame as [Hinv [Horigin Hstack]].
  unfold task_name_set_continuation_masked, task_name_set_continuation_call_binding.
  rewrite Hinv, Horigin.
  entailer!.
Qed.
