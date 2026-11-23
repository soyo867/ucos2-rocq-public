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
From Ucos2Verify.VC.code.task Require Import task_reg_get_goal.
From Ucos2Verify.VC.code.task Require Import task_reg_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_reg_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskRegGet_entail_wit_1_1 : OSTaskRegGet_entail_wit_1_1.
Proof.
  left; intros. Exists entry_2.
  unfold task_reg_get_scalar_valid; entailer!; lia.
Qed.

Lemma proof_of_OSTaskRegGet_entail_wit_1_2 : OSTaskRegGet_entail_wit_1_2.
Proof.
  left; intros. Exists entry_2.
  unfold task_reg_get_scalar_valid; entailer!; lia.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_1 : OSTaskRegGet_return_wit_1.
Proof.
  left; intros.
  pose proof (proj2 (proj1 (proj2 PreH3))) as Hmask.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 0 observed after_2).
  { eapply task_reg_get_call_post_read__read_and_observation with
      (entry := entry_3) (saved := cpu_sr) (pointer := ptcb) (residual := residual_2);
      try eassumption; auto. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 0 observed after_2 X Hpost ltac:(assumption)) as Hsafe.
  rewrite Hmask; Exists 0 after_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_2 : OSTaskRegGet_return_wit_2.
Proof.
  left; intros.
  pose proof (proj2 (proj1 (proj2 PreH3))) as Hmask.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 0 observed after_2).
  { eapply task_reg_get_call_post_read__read_and_observation with
      (entry := entry_3) (saved := cpu_sr) (pointer := ptcb) (residual := residual_2);
      try eassumption; auto. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 0 observed after_2 X Hpost ltac:(assumption)) as Hsafe.
  rewrite Hmask; Exists 0 after_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_3 : OSTaskRegGet_return_wit_3.
Proof.
  left; intros.
  pose proof (proj2 (proj1 (proj2 PreH4))) as Hmask.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2).
  { eapply task_reg_get_call_post_missing__read_and_observation;
      try eassumption; auto. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2 X Hpost ltac:(assumption)) as Hsafe.
  rewrite Hmask; Exists 67 after_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_4 : OSTaskRegGet_return_wit_4.
Proof.
  left; intros.
  pose proof (proj2 (proj1 (proj2 PreH4))) as Hmask.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2).
  { eapply task_reg_get_call_post_missing__read_and_observation;
      try eassumption; auto. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2 X Hpost ltac:(assumption)) as Hsafe.
  rewrite Hmask; Exists 67 after_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_5 : OSTaskRegGet_return_wit_5.
Proof.
  left; intros.
  pose proof (proj2 (proj1 (proj2 PreH5))) as Hmask.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2).
  { eapply task_reg_get_call_post_missing__read_and_observation;
      try eassumption; auto. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2 X Hpost ltac:(assumption)) as Hsafe.
  rewrite Hmask; Exists 67 after_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_6 : OSTaskRegGet_return_wit_6.
Proof.
  left; intros.
  pose proof (proj2 (proj1 (proj2 PreH5))) as Hmask.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2).
  { eapply task_reg_get_call_post_missing__read_and_observation;
      try eassumption; auto. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 67 0 after_2 X Hpost ltac:(assumption)) as Hsafe.
  rewrite Hmask; Exists 67 after_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_7 : OSTaskRegGet_return_wit_7.
Proof.
  left; intros.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 8 0 before).
  { apply task_reg_get_call_post_invalid_id__read_and_observation; auto; lia. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 8 0 before X Hpost ltac:(assumption)) as Hsafe.
  Exists 8 before; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_8 : OSTaskRegGet_return_wit_8.
Proof.
  left; intros.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 8 0 before).
  { apply task_reg_get_call_post_invalid_id__read_and_observation; auto; lia. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 8 0 before X Hpost ltac:(assumption)) as Hsafe.
  Exists 8 before; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_return_wit_9 : OSTaskRegGet_return_wit_9.
Proof.
  left; intros.
  assert (Hpost : task_reg_get_call_post critical sg invocation mask before caller
    prio_pre id_pre 42 0 before).
  { apply task_reg_get_call_post_invalid_priority__read_and_observation; auto; lia. }
  pose proof (task_reg_get_safe_return critical sg invocation mask before caller
    prio_pre id_pre 42 0 before X Hpost ltac:(assumption)) as Hsafe.
  Exists 42 before; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_partial_solve_wit_7_pure : OSTaskRegGet_partial_solve_wit_7_pure.
Proof.
  left; intros.
  destruct PreH2 as [_ [[Hsaved _] [_ Hinv]]].
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_partial_solve_wit_8_pure : OSTaskRegGet_partial_solve_wit_8_pure.
Proof.
  left; intros.
  destruct PreH2 as [_ [[Hsaved _] [_ Hinv]]].
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_partial_solve_wit_9_pure : OSTaskRegGet_partial_solve_wit_9_pure.
Proof.
  left; intros.
  destruct PreH3 as [_ [[Hsaved _] [_ Hinv]]].
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_partial_solve_wit_10_pure : OSTaskRegGet_partial_solve_wit_10_pure.
Proof.
  left; intros.
  destruct PreH3 as [_ [[Hsaved _] [_ Hinv]]].
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_partial_solve_wit_15_pure : OSTaskRegGet_partial_solve_wit_15_pure.
Proof.
  left; intros.
  destruct PreH1 as [_ [[Hsaved _] [_ Hinv]]].
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_partial_solve_wit_16_pure : OSTaskRegGet_partial_solve_wit_16_pure.
Proof.
  left; intros.
  destruct PreH1 as [_ [[Hsaved _] [_ Hinv]]].
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_which_implies_wit_1 : OSTaskRegGet_which_implies_wit_1.
Proof.
  left; intros. Exists entry_2.
  rewrite (task_reg_get_current_split_merge sg entry_2).
  pose proof PreH2 as [Hcurrent Htable].
  rewrite Hcurrent; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_which_implies_wit_2 : OSTaskRegGet_which_implies_wit_2.
Proof.
  left; intros. Exists entry_2.
  pose proof PreH1 as [_ [_ [_ Hinv]]].
  rewrite (task_reg_get_current_split_merge sg entry_2).
  pose proof PreH2 as [Hcurrent Htable].
  rewrite Hcurrent.
  assert (Hselect : task_reg_get_selection sg entry_2 prio ptcb).
  { unfold task_reg_get_selection, task_reg_get_pointer.
    rewrite PreH3; exact PreH4. }
  entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_which_implies_wit_3 : OSTaskRegGet_which_implies_wit_3.
Proof.
  left; intros. Exists entry_2.
  sep_apply_l_atomic (task_reg_get_table_split sg entry_2 prio ltac:(lia)).
  pose proof PreH2 as [Hcurrent Htable].
  rewrite Htable; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_which_implies_wit_4 : OSTaskRegGet_which_implies_wit_4.
Proof.
  left; intros. Exists entry_2.
  pose proof PreH1 as [_ [_ [_ Hinv]]].
  assert (Hselect : task_reg_get_selection sg entry_2 prio ptcb).
  { unfold task_reg_get_selection, task_reg_get_pointer.
    assert (Hneq : (prio =? 255) = false) by (apply Z.eqb_neq; lia).
    rewrite Hneq; exact PreH5. }
  unfold task_reg_get_table_frame, task_reg_get_table_pointer, UCOS2_inv.
  rewrite UCOS2_raw_rep_priority_table_equiv.
  pose proof PreH2 as [_ Htable].
  rewrite <- Htable.
  unfold task_reg_get_global_addresses in *.
  entailer!.
  apply (store_prio_tbl_merge_cell sg entry_2.(TskState).(prioTbl) prio
    ltac:(lia)).
Qed.

Lemma proof_of_OSTaskRegGet_which_implies_wit_5 : OSTaskRegGet_which_implies_wit_5.
Proof.
  left; intros.
  destruct PreH3 as [Hprio [Hdomain Hid]].
  destruct (task_reg_get_success_word_view critical sg invocation mask cpu_sr
    before entry_2 caller prio id ptcb PreH1 PreH2 (proj1 Hprio) Hdomain Hid PreH4 PreH5 PreH6)
    as [observed [residual Hview]].
  subst id.
  pose proof (task_reg_get_read_open sg entry_2 caller ptcb observed residual Hview) as Hopen.
  cbn [tcb_field_address] in Hopen.
  cbn [Z.mul]; rewrite Z.add_0_r.
  sep_apply_l_atomic Hopen; Intros.
  Exists observed residual entry_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegGet_which_implies_wit_6 : OSTaskRegGet_which_implies_wit_6.
Proof.
  left; intros; subst id.
  pose proof (proj2 (proj2 (proj2 PreH1))) as Hvalid.
  pose proof (task_reg_get_read_close sg entry_2 caller ptcb observed residual_2
    Hvalid PreH6) as Hclose.
  cbn [tcb_field_address] in Hclose.
  cbn [Z.mul]; rewrite Z.add_0_r.
  sep_apply_l_atomic Hclose.
  Exists residual_2 entry_2; entailer!.
Qed.

