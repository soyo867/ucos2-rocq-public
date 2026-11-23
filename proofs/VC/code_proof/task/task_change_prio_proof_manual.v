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
From Ucos2Verify.VC.code.task Require Import task_change_prio_goal.
From Ucos2Verify.VC.code.task Require Import task_change_prio_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskChangePrio_safety_wit_23 : OSTaskChangePrio_safety_wit_23.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_safety_wit_24 : OSTaskChangePrio_safety_wit_24.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_safety_wit_25 : OSTaskChangePrio_safety_wit_25.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hx; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_safety_wit_26 : OSTaskChangePrio_safety_wit_26.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hx; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_1_1 : OSTaskChangePrio_entail_wit_1_1.
Proof.
  unfold OSTaskChangePrio_entail_wit_1_1; left; intros.
  assert (Hargument : task_change_priority_argument_error sg requested destination = None).
  { eapply task_change_prio_argument_valid__call_boundaries;
      [exact PreH1|exact PreH11|right; lia|lia]. }
  destruct (PreH14 Hargument) as [Hsource Hadmission].
  unfold task_change_prio_save_post; Intros returned acquired.
  assert (Hsave : task_change_prio_save_source environment critical sg requested destination
    execution returned mask retval before acquired) by assumption.
  destruct (task_change_prio_save_transports_call_source__call_boundaries
    environment critical sg requested destination execution returned mask retval before acquired
    PreH1 PreH13 Hsource Hsave) as [Henv [Hsaved [Hvalid Hcall]]].
  destruct (Hadmission returned retval acquired (proj2 Hsave)) as [Howner Hself].
  rewrite PreH5, PreH6.
  Exists acquired returned; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_1_2 : OSTaskChangePrio_entail_wit_1_2.
Proof.
  unfold OSTaskChangePrio_entail_wit_1_2; left; intros.
  assert (Hargument : task_change_priority_argument_error sg requested destination = None).
  { eapply task_change_prio_argument_valid__call_boundaries;
      [exact PreH1|exact PreH10|left; lia|lia]. }
  destruct (PreH13 Hargument) as [Hsource Hadmission].
  unfold task_change_prio_save_post; Intros returned acquired.
  assert (Hsave : task_change_prio_save_source environment critical sg requested destination
    execution returned mask retval before acquired) by assumption.
  destruct (task_change_prio_save_transports_call_source__call_boundaries
    environment critical sg requested destination execution returned mask retval before acquired
    PreH1 PreH12 Hsource Hsave) as [Henv [Hsaved [Hvalid Hcall]]].
  destruct (Hadmission returned retval acquired (proj2 Hsave)) as [Howner Hself].
  rewrite PreH4, PreH5.
  Exists acquired returned; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_2_1 : OSTaskChangePrio_entail_wit_2_1.
Proof.
  unfold OSTaskChangePrio_entail_wit_2_1; left; intros.
  pose proof (proj1 (proj1 PreH15)) as Hsg.
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold Ucos2Verify.lib.stable_glob_vars.valid_stable_glob_vars in Hsg; tauto).
  assert (Hself : sg.(osPrioSelf) = 255)
    by (unfold Ucos2Verify.lib.stable_glob_vars.valid_stable_glob_vars in Hsg; tauto).
  destruct PreH1 as [Hcurrent Hnode].
  assert (Hrange : 0 <= current_node.(curPrio) <= 63).
  { pose proof (proj1 (proj2 PreH15)) as Htasks.
    destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hrange _]]]]]]]].
    specialize (Hrange current_tid current_node Hnode).
    unfold Ucos2Verify.lib.stable_glob_vars.task_priority_in_range in Hrange;
      rewrite Hlowest in Hrange; exact Hrange. }
  assert (Hselection : task_change_priority_selection sg acquired requested current_node.(curPrio)).
  { left; split; [congruence|]. exists current_tid, current_node; auto. }
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_2_2 : OSTaskChangePrio_entail_wit_2_2.
Proof.
  unfold OSTaskChangePrio_entail_wit_2_2; left; intros.
  pose proof (proj1 (proj1 PreH14)) as Hsg.
  assert (Hself : sg.(osPrioSelf) = 255)
    by (unfold Ucos2Verify.lib.stable_glob_vars.valid_stable_glob_vars in Hsg; tauto).
  assert (Hselection : task_change_priority_selection sg acquired requested requested).
  { right; split; [congruence|reflexivity]. }
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_3_1 : OSTaskChangePrio_entail_wit_3_1.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy, Hx, Hby, Hbx.
  assert (Htable :
    replace_Znth destination (Znth oldprio (task_change_prio_table sg acquired) 0)
      (replace_Znth oldprio 0 (task_change_prio_table sg acquired)) =
    task_change_prio_updated_table sg acquired target_tid target_node oldprio destination).
  { rewrite PreH9.
    apply priority_table_writes_eq__priority_arithmetic; lia. }
  rewrite Htable.
  pose proof (single_bit_in_byte_range__ready_bitmap_stages
    (tcb_x_of_prio (curPrio target_node)) ltac:(lia)) as Hbit.
  change (0 <= tcb_bit_x_of_prio (curPrio target_node) < 256) in Hbit.
  assert (Hbit32 : unsigned_last_nbits (tcb_bit_x_of_prio (curPrio target_node)) 32 =
    tcb_bit_x_of_prio (curPrio target_node)).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hbit32 in PreH2.
  assert (Hready : mutex_priority_was_ready (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)) =
    true).
  { unfold mutex_priority_was_ready.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2); reflexivity. }
  unfold mutex_priority_rows, mutex_priority_group, mutex_priority_removed_rows.
  rewrite Hready.
  fold (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))) in *.
  pose proof (ready_cleared_row_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    ltac:(lia)) as Hclearr.
  pose proof (ready_replaced_rows_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    (tcb_y_of_prio destination) ltac:(lia) Hyr) as Hremovedr.
  rewrite Znth_replace_Znth_Same in PreH1 by
    (rewrite ready_rows_length__priority_arithmetic; lia).
  rewrite unsigned_last_nbits_eq in PreH1 by
    (split; [exact (proj1 Hclearr)|
      eapply Z.lt_le_trans; [exact (proj2 Hclearr)|lia]]).
  unfold ready_group_after_relocation.
  rewrite (proj2 (Z.eqb_eq _ _) PreH1).
  rewrite (unsigned_last_nbits_eq
    (Znth (tcb_y_of_prio destination)
      (replace_Znth (tcb_y_of_prio (curPrio target_node))
        (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
          (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)))
        (task_change_prio_ready_rows acquired)) 0) 8) by exact Hremovedr.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_3_2 : OSTaskChangePrio_entail_wit_3_2.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy, Hx, Hby, Hbx.
  assert (Htable :
    replace_Znth destination (Znth oldprio (task_change_prio_table sg acquired) 0)
      (replace_Znth oldprio 0 (task_change_prio_table sg acquired)) =
    task_change_prio_updated_table sg acquired target_tid target_node oldprio destination).
  { rewrite PreH9.
    apply priority_table_writes_eq__priority_arithmetic; lia. }
  rewrite Htable.
  pose proof (single_bit_in_byte_range__ready_bitmap_stages
    (tcb_x_of_prio (curPrio target_node)) ltac:(lia)) as Hbit.
  change (0 <= tcb_bit_x_of_prio (curPrio target_node) < 256) in Hbit.
  assert (Hbit32 : unsigned_last_nbits (tcb_bit_x_of_prio (curPrio target_node)) 32 =
    tcb_bit_x_of_prio (curPrio target_node)).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hbit32 in PreH2.
  assert (Hready : mutex_priority_was_ready (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)) =
    true).
  { unfold mutex_priority_was_ready.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2); reflexivity. }
  unfold mutex_priority_rows, mutex_priority_group, mutex_priority_removed_rows.
  rewrite Hready.
  fold (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))) in *.
  pose proof (ready_cleared_row_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    ltac:(lia)) as Hclearr.
  pose proof (ready_replaced_rows_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    (tcb_y_of_prio destination) ltac:(lia) Hyr) as Hremovedr.
  rewrite Znth_replace_Znth_Same in PreH1 by
    (rewrite ready_rows_length__priority_arithmetic; lia).
  rewrite unsigned_last_nbits_eq in PreH1 by
    (split; [exact (proj1 Hclearr)|
      eapply Z.lt_le_trans; [exact (proj2 Hclearr)|lia]]).
  unfold ready_group_after_relocation.
  rewrite (proj2 (Z.eqb_eq _ _) PreH1).
  rewrite (unsigned_last_nbits_eq
    (Znth (tcb_y_of_prio destination)
      (replace_Znth (tcb_y_of_prio (curPrio target_node))
        (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
          (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)))
        (task_change_prio_ready_rows acquired)) 0) 8) by exact Hremovedr.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_3_3 : OSTaskChangePrio_entail_wit_3_3.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy, Hx, Hby, Hbx.
  assert (Htable :
    replace_Znth destination (Znth oldprio (task_change_prio_table sg acquired) 0)
      (replace_Znth oldprio 0 (task_change_prio_table sg acquired)) =
    task_change_prio_updated_table sg acquired target_tid target_node oldprio destination).
  { rewrite PreH9.
    apply priority_table_writes_eq__priority_arithmetic; lia. }
  rewrite Htable.
  pose proof (single_bit_in_byte_range__ready_bitmap_stages
    (tcb_x_of_prio (curPrio target_node)) ltac:(lia)) as Hbit.
  change (0 <= tcb_bit_x_of_prio (curPrio target_node) < 256) in Hbit.
  assert (Hbit32 : unsigned_last_nbits (tcb_bit_x_of_prio (curPrio target_node)) 32 =
    tcb_bit_x_of_prio (curPrio target_node)).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hbit32 in PreH2.
  assert (Hready : mutex_priority_was_ready (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)) =
    true).
  { unfold mutex_priority_was_ready.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2); reflexivity. }
  unfold mutex_priority_rows, mutex_priority_group, mutex_priority_removed_rows.
  rewrite Hready.
  fold (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))) in *.
  pose proof (ready_cleared_row_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    ltac:(lia)) as Hclearr.
  pose proof (ready_replaced_rows_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    (tcb_y_of_prio destination) ltac:(lia) Hyr) as Hremovedr.
  rewrite Znth_replace_Znth_Same in PreH1 by
    (rewrite ready_rows_length__priority_arithmetic; lia).
  rewrite unsigned_last_nbits_eq in PreH1 by
    (split; [exact (proj1 Hclearr)|
      eapply Z.lt_le_trans; [exact (proj2 Hclearr)|lia]]).
  unfold ready_group_after_relocation.
  rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  rewrite (unsigned_last_nbits_eq
    (Znth (tcb_y_of_prio destination)
      (replace_Znth (tcb_y_of_prio (curPrio target_node))
        (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
          (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)))
        (task_change_prio_ready_rows acquired)) 0) 8) by exact Hremovedr.
  rewrite (unsigned_last_nbits_eq (task_change_prio_ready_group acquired) 8) by
    (eapply ready_group_in_range__priority_arithmetic; eassumption).
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_3_4 : OSTaskChangePrio_entail_wit_3_4.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy, Hx, Hby, Hbx.
  assert (Htable :
    replace_Znth destination (Znth oldprio (task_change_prio_table sg acquired) 0)
      (replace_Znth oldprio 0 (task_change_prio_table sg acquired)) =
    task_change_prio_updated_table sg acquired target_tid target_node oldprio destination).
  { rewrite PreH9.
    apply priority_table_writes_eq__priority_arithmetic; lia. }
  rewrite Htable.
  pose proof (single_bit_in_byte_range__ready_bitmap_stages
    (tcb_x_of_prio (curPrio target_node)) ltac:(lia)) as Hbit.
  change (0 <= tcb_bit_x_of_prio (curPrio target_node) < 256) in Hbit.
  assert (Hbit32 : unsigned_last_nbits (tcb_bit_x_of_prio (curPrio target_node)) 32 =
    tcb_bit_x_of_prio (curPrio target_node)).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hbit32 in PreH2.
  assert (Hready : mutex_priority_was_ready (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)) =
    true).
  { unfold mutex_priority_was_ready.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2); reflexivity. }
  unfold mutex_priority_rows, mutex_priority_group, mutex_priority_removed_rows.
  rewrite Hready.
  fold (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))) in *.
  pose proof (ready_cleared_row_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    ltac:(lia)) as Hclearr.
  pose proof (ready_replaced_rows_in_range__priority_arithmetic acquired
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node))
    (tcb_y_of_prio destination) ltac:(lia) Hyr) as Hremovedr.
  rewrite Znth_replace_Znth_Same in PreH1 by
    (rewrite ready_rows_length__priority_arithmetic; lia).
  rewrite unsigned_last_nbits_eq in PreH1 by
    (split; [exact (proj1 Hclearr)|
      eapply Z.lt_le_trans; [exact (proj2 Hclearr)|lia]]).
  unfold ready_group_after_relocation.
  rewrite (proj2 (Z.eqb_neq _ _) PreH1).
  rewrite (unsigned_last_nbits_eq
    (Znth (tcb_y_of_prio destination)
      (replace_Znth (tcb_y_of_prio (curPrio target_node))
        (mutex_priority_cleared_row (task_change_prio_ready_rows acquired)
          (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)))
        (task_change_prio_ready_rows acquired)) 0) 8) by exact Hremovedr.
  rewrite (unsigned_last_nbits_eq (task_change_prio_ready_group acquired) 8) by
    (eapply ready_group_in_range__priority_arithmetic; eassumption).
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_3_5 : OSTaskChangePrio_entail_wit_3_5.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy, Hx, Hby, Hbx.
  assert (Htable :
    replace_Znth destination (Znth oldprio (task_change_prio_table sg acquired) 0)
      (replace_Znth oldprio 0 (task_change_prio_table sg acquired)) =
    task_change_prio_updated_table sg acquired target_tid target_node oldprio destination).
  { rewrite PreH8.
    apply priority_table_writes_eq__priority_arithmetic; lia. }
  rewrite Htable.
  pose proof (single_bit_in_byte_range__ready_bitmap_stages
    (tcb_x_of_prio (curPrio target_node)) ltac:(lia)) as Hbit.
  change (0 <= tcb_bit_x_of_prio (curPrio target_node) < 256) in Hbit.
  assert (Hbit32 : unsigned_last_nbits (tcb_bit_x_of_prio (curPrio target_node)) 32 =
    tcb_bit_x_of_prio (curPrio target_node)).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hbit32 in PreH1.
  assert (Hready : mutex_priority_was_ready (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)) =
    false).
  { unfold mutex_priority_was_ready.
    rewrite (proj2 (Z.eqb_eq _ _) PreH1); reflexivity. }
  unfold mutex_priority_rows, mutex_priority_group.
  rewrite Hready.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_3_6 : OSTaskChangePrio_entail_wit_3_6.
Proof.
  left; intros.
  destruct (priority_coordinates_eq__priority_arithmetic destination ltac:(lia))
    as [Hy [Hx [Hyr [Hxr [Hby Hbx]]]]].
  rewrite Hy, Hx, Hby, Hbx.
  assert (Htable :
    replace_Znth destination (Znth oldprio (task_change_prio_table sg acquired) 0)
      (replace_Znth oldprio 0 (task_change_prio_table sg acquired)) =
    task_change_prio_updated_table sg acquired target_tid target_node oldprio destination).
  { rewrite PreH8.
    apply priority_table_writes_eq__priority_arithmetic; lia. }
  rewrite Htable.
  pose proof (single_bit_in_byte_range__ready_bitmap_stages
    (tcb_x_of_prio (curPrio target_node)) ltac:(lia)) as Hbit.
  change (0 <= tcb_bit_x_of_prio (curPrio target_node) < 256) in Hbit.
  assert (Hbit32 : unsigned_last_nbits (tcb_bit_x_of_prio (curPrio target_node)) 32 =
    tcb_bit_x_of_prio (curPrio target_node)).
  { apply unsigned_last_nbits_eq; cbn; lia. }
  rewrite Hbit32 in PreH1.
  assert (Hready : mutex_priority_was_ready (task_change_prio_ready_rows acquired)
    (tcb_y_of_prio (curPrio target_node)) (tcb_bit_x_of_prio (curPrio target_node)) =
    false).
  { unfold mutex_priority_was_ready.
    rewrite (proj2 (Z.eqb_eq _ _) PreH1); reflexivity. }
  unfold mutex_priority_rows, mutex_priority_group.
  rewrite Hready.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_4_1 : OSTaskChangePrio_entail_wit_4_1.
Proof.
  left; intros; subst y_new bity_new bitx_new.
  assert (Hlen : Zlength (task_change_prio_event_rows acquired waiting_event) = 8).
  { apply task_change_prio_event_rows_length__event_rows. }
  assert (Hrows : forall y, 0 <= y < 8 ->
    0 <= Znth y (task_change_prio_event_rows acquired waiting_event) 0 < 256).
  { intros; apply task_change_prio_event_rows_in_range__event_rows; assumption. }
  assert (Hwas : mutex_priority_was_ready (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) = true).
  { unfold mutex_priority_was_ready; apply negb_true_iff, Z.eqb_neq; exact PreH7. }
  pose proof (bitmap_cleared_row_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio))
    Hlen ltac:(lia) (Hrows (tcb_y_of_prio target_node.(curPrio)) ltac:(lia))) as Hclear.
  lazymatch type of Hclear with ?lhs = _ => change (lhs = 0) in PreH1 end.
  rewrite Hclear in PreH1.
  assert (Hbit : unsigned_last_nbits (tcb_bit_y_of_prio destination) 8 = tcb_bit_y_of_prio destination).
  { unfold tcb_bit_y_of_prio; apply shift_one_unsigned_byte_eq__priority_encoding.
    destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding destination ltac:(lia))
      as [_ [Hy _]]; exact Hy. }
  assert (Hgroup :
    Z.lor (Z.land (task_change_prio_event_group acquired waiting_event)
      (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio target_node.(curPrio))) 8))
      (unsigned_last_nbits (tcb_bit_y_of_prio destination) 8) =
    mutex_priority_group (task_change_prio_event_rows acquired waiting_event)
      (task_change_prio_event_group acquired waiting_event) (tcb_y_of_prio target_node.(curPrio))
      (tcb_bit_x_of_prio target_node.(curPrio)) (tcb_bit_y_of_prio target_node.(curPrio)) destination).
  { unfold mutex_priority_group; rewrite Hwas; unfold ready_group_after_relocation.
    rewrite PreH1, Z.eqb_refl, Hbit; reflexivity. }
  rewrite PreH2, Hgroup.
  pose proof (bitmap_relocated_rows_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination
    Hlen ltac:(lia) ltac:(lia) Hrows PreH7) as Hrelocated.
  unfold mutex_priority_cleared_row in Hrelocated.
  lazymatch goal with
  | |- context [UCharArray.full ?address 8 ?actual] =>
      assert (Hactual_rows : actual = mutex_priority_rows
        (task_change_prio_event_rows acquired waiting_event)
        (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination)
        by exact Hrelocated
  end.
  rewrite Hactual_rows.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_4_2 : OSTaskChangePrio_entail_wit_4_2.
Proof.
  left; intros; subst y_new bity_new bitx_new.
  assert (Hlen : Zlength (task_change_prio_event_rows acquired waiting_event) = 8).
  { apply task_change_prio_event_rows_length__event_rows. }
  assert (Hrows : forall y, 0 <= y < 8 ->
    0 <= Znth y (task_change_prio_event_rows acquired waiting_event) 0 < 256).
  { intros; apply task_change_prio_event_rows_in_range__event_rows; assumption. }
  assert (Hwas : mutex_priority_was_ready (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) = true).
  { unfold mutex_priority_was_ready; apply negb_true_iff, Z.eqb_neq; exact PreH7. }
  pose proof (bitmap_cleared_row_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio))
    Hlen ltac:(lia) (Hrows (tcb_y_of_prio target_node.(curPrio)) ltac:(lia))) as Hclear.
  lazymatch type of Hclear with ?lhs = _ => change (lhs = 0) in PreH1 end.
  rewrite Hclear in PreH1.
  assert (Hbit : unsigned_last_nbits (tcb_bit_y_of_prio destination) 8 = tcb_bit_y_of_prio destination).
  { unfold tcb_bit_y_of_prio; apply shift_one_unsigned_byte_eq__priority_encoding.
    destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding destination ltac:(lia))
      as [_ [Hy _]]; exact Hy. }
  assert (Hgroup :
    Z.lor (Z.land (task_change_prio_event_group acquired waiting_event)
      (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio target_node.(curPrio))) 8))
      (unsigned_last_nbits (tcb_bit_y_of_prio destination) 8) =
    mutex_priority_group (task_change_prio_event_rows acquired waiting_event)
      (task_change_prio_event_group acquired waiting_event) (tcb_y_of_prio target_node.(curPrio))
      (tcb_bit_x_of_prio target_node.(curPrio)) (tcb_bit_y_of_prio target_node.(curPrio)) destination).
  { unfold mutex_priority_group; rewrite Hwas; unfold ready_group_after_relocation.
    rewrite PreH1, Z.eqb_refl, Hbit; reflexivity. }
  rewrite PreH2, Hgroup.
  pose proof (bitmap_relocated_rows_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination
    Hlen ltac:(lia) ltac:(lia) Hrows PreH7) as Hrelocated.
  unfold mutex_priority_cleared_row in Hrelocated.
  lazymatch goal with
  | |- context [UCharArray.full ?address 8 ?actual] =>
      assert (Hactual_rows : actual = mutex_priority_rows
        (task_change_prio_event_rows acquired waiting_event)
        (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination)
        by exact Hrelocated
  end.
  rewrite Hactual_rows.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_4_3 : OSTaskChangePrio_entail_wit_4_3.
Proof.
  left; intros; subst y_new bity_new bitx_new.
  assert (Hlen : Zlength (task_change_prio_event_rows acquired waiting_event) = 8).
  { apply task_change_prio_event_rows_length__event_rows. }
  assert (Hrows : forall y, 0 <= y < 8 ->
    0 <= Znth y (task_change_prio_event_rows acquired waiting_event) 0 < 256).
  { intros; apply task_change_prio_event_rows_in_range__event_rows; assumption. }
  assert (Hwas : mutex_priority_was_ready (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) = true).
  { unfold mutex_priority_was_ready; apply negb_true_iff, Z.eqb_neq; exact PreH7. }
  pose proof (bitmap_cleared_row_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio))
    Hlen ltac:(lia) (Hrows (tcb_y_of_prio target_node.(curPrio)) ltac:(lia))) as Hclear.
  lazymatch type of Hclear with ?lhs = _ => change (lhs <> 0) in PreH1 end.
  rewrite Hclear in PreH1.
  assert (Hbit : unsigned_last_nbits (tcb_bit_y_of_prio destination) 8 = tcb_bit_y_of_prio destination).
  { unfold tcb_bit_y_of_prio; apply shift_one_unsigned_byte_eq__priority_encoding.
    destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding destination ltac:(lia))
      as [_ [Hy _]]; exact Hy. }
  assert (Hgroup :
    Z.lor (task_change_prio_event_group acquired waiting_event)
      (unsigned_last_nbits (tcb_bit_y_of_prio destination) 8) =
    mutex_priority_group (task_change_prio_event_rows acquired waiting_event)
      (task_change_prio_event_group acquired waiting_event) (tcb_y_of_prio target_node.(curPrio))
      (tcb_bit_x_of_prio target_node.(curPrio)) (tcb_bit_y_of_prio target_node.(curPrio)) destination).
  { unfold mutex_priority_group; rewrite Hwas; unfold ready_group_after_relocation.
    assert (Hzero : Z.eqb (mutex_priority_cleared_row
      (task_change_prio_event_rows acquired waiting_event)
      (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio))) 0 = false)
      by (apply Z.eqb_neq; exact PreH1).
    lazymatch goal with
    | |- context [if ?condition then _ else _] =>
        assert (Hactual_zero : condition = false) by exact Hzero
    end.
    rewrite Hactual_zero, Hbit; reflexivity. }
  pose proof (task_change_prio_event_group_in_range__event_rows
    sg acquired waiting_eid waiting_event PreH20 (proj2 PreH3)) as Hgroup_range.
  rewrite (unsigned_last_nbits_eq _ 8 Hgroup_range), PreH2, Hgroup.
  pose proof (bitmap_relocated_rows_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination
    Hlen ltac:(lia) ltac:(lia) Hrows PreH7) as Hrelocated.
  unfold mutex_priority_cleared_row in Hrelocated.
  lazymatch goal with
  | |- context [UCharArray.full ?address 8 ?actual] =>
      assert (Hactual_rows : actual = mutex_priority_rows
        (task_change_prio_event_rows acquired waiting_event)
        (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination)
        by exact Hrelocated
  end.
  rewrite Hactual_rows.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_4_4 : OSTaskChangePrio_entail_wit_4_4.
Proof.
  left; intros; subst y_new bity_new bitx_new.
  assert (Hlen : Zlength (task_change_prio_event_rows acquired waiting_event) = 8).
  { apply task_change_prio_event_rows_length__event_rows. }
  assert (Hrows : forall y, 0 <= y < 8 ->
    0 <= Znth y (task_change_prio_event_rows acquired waiting_event) 0 < 256).
  { intros; apply task_change_prio_event_rows_in_range__event_rows; assumption. }
  assert (Hwas : mutex_priority_was_ready (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) = true).
  { unfold mutex_priority_was_ready; apply negb_true_iff, Z.eqb_neq; exact PreH7. }
  pose proof (bitmap_cleared_row_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio))
    Hlen ltac:(lia) (Hrows (tcb_y_of_prio target_node.(curPrio)) ltac:(lia))) as Hclear.
  lazymatch type of Hclear with ?lhs = _ => change (lhs <> 0) in PreH1 end.
  rewrite Hclear in PreH1.
  assert (Hbit : unsigned_last_nbits (tcb_bit_y_of_prio destination) 8 = tcb_bit_y_of_prio destination).
  { unfold tcb_bit_y_of_prio; apply shift_one_unsigned_byte_eq__priority_encoding.
    destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding destination ltac:(lia))
      as [_ [Hy _]]; exact Hy. }
  assert (Hgroup :
    Z.lor (task_change_prio_event_group acquired waiting_event)
      (unsigned_last_nbits (tcb_bit_y_of_prio destination) 8) =
    mutex_priority_group (task_change_prio_event_rows acquired waiting_event)
      (task_change_prio_event_group acquired waiting_event) (tcb_y_of_prio target_node.(curPrio))
      (tcb_bit_x_of_prio target_node.(curPrio)) (tcb_bit_y_of_prio target_node.(curPrio)) destination).
  { unfold mutex_priority_group; rewrite Hwas; unfold ready_group_after_relocation.
    assert (Hzero : Z.eqb (mutex_priority_cleared_row
      (task_change_prio_event_rows acquired waiting_event)
      (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio))) 0 = false)
      by (apply Z.eqb_neq; exact PreH1).
    lazymatch goal with
    | |- context [if ?condition then _ else _] =>
        assert (Hactual_zero : condition = false) by exact Hzero
    end.
    rewrite Hactual_zero, Hbit; reflexivity. }
  pose proof (task_change_prio_event_group_in_range__event_rows
    sg acquired waiting_eid waiting_event PreH20 (proj2 PreH3)) as Hgroup_range.
  rewrite (unsigned_last_nbits_eq _ 8 Hgroup_range), PreH2, Hgroup.
  pose proof (bitmap_relocated_rows_unsigned_eq__event_rows
    (task_change_prio_event_rows acquired waiting_event)
    (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination
    Hlen ltac:(lia) ltac:(lia) Hrows PreH7) as Hrelocated.
  unfold mutex_priority_cleared_row in Hrelocated.
  lazymatch goal with
  | |- context [UCharArray.full ?address 8 ?actual] =>
      assert (Hactual_rows : actual = mutex_priority_rows
        (task_change_prio_event_rows acquired waiting_event)
        (tcb_y_of_prio target_node.(curPrio)) (tcb_bit_x_of_prio target_node.(curPrio)) destination)
        by exact Hrelocated
  end.
  rewrite Hactual_rows.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_5_1 : OSTaskChangePrio_entail_wit_5_1.
Proof.
  left; intros.
  destruct PreH30 as [Hpointer Hevent].
  assert (Haddress : pevent = task_change_prio_event_pointer sg target_node).
  { unfold task_change_prio_event_pointer; rewrite Hpointer; exact PreH29. }
  rewrite Haddress; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_5_2 : OSTaskChangePrio_entail_wit_5_2.
Proof.
  left; intros.
  destruct PreH30 as [Hpointer Hevent].
  assert (Haddress : pevent = task_change_prio_event_pointer sg target_node).
  { unfold task_change_prio_event_pointer; rewrite Hpointer; exact PreH29. }
  rewrite Haddress; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_5_3 : OSTaskChangePrio_entail_wit_5_3.
Proof.
  left; intros.
  pose proof (task_change_prio_event_pointer_zero__event_rows
    sg acquired requested oldprio destination target_tid target_node PreH18 PreH1) as Hnone.
  unfold task_change_prio_event_storage; rewrite Hnone; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_5_4 : OSTaskChangePrio_entail_wit_5_4.
Proof.
  left; intros.
  pose proof (task_change_prio_event_pointer_zero__event_rows
    sg acquired requested oldprio destination target_tid target_node PreH18 PreH1) as Hnone.
  unfold task_change_prio_event_storage; rewrite Hnone; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_6_1 : OSTaskChangePrio_entail_wit_6_1.
Proof.
  left; intros; subst y_new x_new bity_new bitx_new.
  pose proof PreH18 as [_ [_ [_ [_ [Hnode _]]]]].
  pose proof (task_change_prio_current_cache_byte_eq
    sg acquired target_tid target_node destination PreH13 Hnode) as Hcache.
  assert (Htest : Z.eqb (task_slot_addr sg target_tid)
    (encode_task_link sg acquired.(SchedState).(curTaskID)) = true).
  { apply Z.eqb_eq; congruence. }
  rewrite Htest in Hcache.
  rewrite Hcache; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_6_2 : OSTaskChangePrio_entail_wit_6_2.
Proof.
  left; intros; subst y_new x_new bity_new bitx_new.
  pose proof PreH18 as [_ [_ [_ [_ [Hnode _]]]]].
  pose proof (task_change_prio_current_cache_byte_eq
    sg acquired target_tid target_node destination PreH13 Hnode) as Hcache.
  assert (Htest : Z.eqb (task_slot_addr sg target_tid)
    (encode_task_link sg acquired.(SchedState).(curTaskID)) = true).
  { apply Z.eqb_eq; congruence. }
  rewrite Htest in Hcache.
  rewrite Hcache; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_6_3 : OSTaskChangePrio_entail_wit_6_3.
Proof.
  left; intros; subst y_new x_new bity_new bitx_new.
  pose proof PreH18 as [_ [_ [_ [_ [Hnode _]]]]].
  pose proof (task_change_prio_current_cache_byte_eq
    sg acquired target_tid target_node destination PreH13 Hnode) as Hcache.
  assert (Htest : Z.eqb (task_slot_addr sg target_tid)
    (encode_task_link sg acquired.(SchedState).(curTaskID)) = false).
  { apply Z.eqb_neq; congruence. }
  rewrite Htest in Hcache.
  rewrite Hcache; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_6_4 : OSTaskChangePrio_entail_wit_6_4.
Proof.
  left; intros; subst y_new x_new bity_new bitx_new.
  pose proof PreH18 as [_ [_ [_ [_ [Hnode _]]]]].
  pose proof (task_change_prio_current_cache_byte_eq
    sg acquired target_tid target_node destination PreH13 Hnode) as Hcache.
  assert (Htest : Z.eqb (task_slot_addr sg target_tid)
    (encode_task_link sg acquired.(SchedState).(curTaskID)) = false).
  { apply Z.eqb_neq; congruence. }
  rewrite Htest in Hcache.
  rewrite Hcache; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_7_1 : OSTaskChangePrio_entail_wit_7_1.
Proof.
  left; intros; subst ptcb y_new x_new bity_new bitx_new.
  pose proof PreH17 as [_ [_ [_ [_ [Hold _]]]]].
  pose proof (task_change_prio_preserves_state_inv__task_state
    sg acquired requested target_tid target_node oldprio destination PreH17) as Hvalid.
  pose proof (task_change_prio_preserves_call_source__task_state
    sg acquired acquired_execution target_tid target_node oldprio destination Hold PreH13) as Hsource.
  pose proof (task_change_prio_live_critical_code__task_state
    sg acquired requested target_tid target_node oldprio destination PreH17) as Hcode.
  pose proof (task_change_prio_work_merge_updated__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired requested
    target_tid target_node oldprio destination PreH7 PreH17) as Hmerge.
  pose proof PreH8 as [Htable [Hcurrent [Hgroup [Hrows [_ Hscheduler]]]]].
  pose proof Hscheduler as [_ [_ [_ [Hpriority _]]]].
  rewrite Htable, Hcurrent, Hgroup, Hrows, <- Hpriority in Hmerge.
  cbn [tcb_field_address] in Hmerge.
  entailer!.
  sep_apply_r_atomic Hmerge; entailer!.
  repeat (sep_apply store_ptr_undef_store_ptr).
  repeat (sep_apply store_uchar_undef_store_uchar).
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_7_2 : OSTaskChangePrio_entail_wit_7_2.
Proof.
  left; intros; subst ptcb y_new x_new bity_new bitx_new.
  pose proof PreH17 as [_ [_ [_ [_ [Hold _]]]]].
  pose proof (task_change_prio_preserves_state_inv__task_state
    sg acquired requested target_tid target_node oldprio destination PreH17) as Hvalid.
  pose proof (task_change_prio_preserves_call_source__task_state
    sg acquired acquired_execution target_tid target_node oldprio destination Hold PreH13) as Hsource.
  pose proof (task_change_prio_live_critical_code__task_state
    sg acquired requested target_tid target_node oldprio destination PreH17) as Hcode.
  pose proof (task_change_prio_work_merge_updated__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired requested
    target_tid target_node oldprio destination PreH7 PreH17) as Hmerge.
  pose proof PreH8 as [Htable [Hcurrent [Hgroup [Hrows [_ Hscheduler]]]]].
  pose proof Hscheduler as [_ [_ [_ [Hpriority _]]]].
  rewrite Htable, Hcurrent, Hgroup, Hrows, <- Hpriority in Hmerge.
  cbn [tcb_field_address] in Hmerge.
  entailer!.
  sep_apply_r_atomic Hmerge; entailer!.
  repeat (sep_apply store_ptr_undef_store_ptr).
  repeat (sep_apply store_uchar_undef_store_uchar).
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_8_1 : OSTaskChangePrio_entail_wit_8_1.
Proof.
  unfold OSTaskChangePrio_entail_wit_8_1; left; intros.
  unfold task_change_prio_restore_post; Intros returned current.
  assert (Hrestore : task_change_prio_restore_source environment critical sg
    acquired_execution returned
    (task_change_priority_state sg acquired target_tid target_node oldprio destination) current)
    by assumption.
  destruct (task_change_prio_restore_transports_call_source__call_boundaries
    environment critical sg requested destination acquired_execution returned _ current
    PreH18 PreH9 PreH19 Hrestore) as [Henv Hcall].
  rewrite (proj2 PreH11).
  Exists returned current; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_entail_wit_8_2 : OSTaskChangePrio_entail_wit_8_2.
Proof.
  unfold OSTaskChangePrio_entail_wit_8_2; left; intros.
  unfold task_change_prio_restore_post; Intros returned current.
  assert (Hrestore : task_change_prio_restore_source environment critical sg
    acquired_execution returned
    (task_change_priority_state sg acquired target_tid target_node oldprio destination) current)
    by assumption.
  destruct (task_change_prio_restore_transports_call_source__call_boundaries
    environment critical sg requested destination acquired_execution returned _ current
    PreH18 PreH9 PreH19 Hrestore) as [Henv Hcall].
  rewrite (proj2 PreH11).
  Exists returned current; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_1 : OSTaskChangePrio_return_wit_1.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 0 X PreH3).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH14 ltac:(lia) PreH8) as Harguments.
  assert (Hrunning : restored.(SchedState).(isRunning) = true).
  { unfold task_change_prio_running in PreH2.
    destruct restored.(SchedState).(isRunning); [reflexivity|].
    vm_compute in PreH2; discriminate. }
  unfold task_change_prio_post; rewrite Harguments.
  Exists cpu_sr acquired_execution acquired
    (task_change_priority_state sg acquired target_tid target_node oldprio destination)
    restored_execution restored.
  rewrite Hrunning; cbn [Z.eqb andb]; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_2 : OSTaskChangePrio_return_wit_2.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 0 X PreH3).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH14 ltac:(lia) PreH8) as Harguments.
  assert (Hrunning : restored.(SchedState).(isRunning) = true).
  { unfold task_change_prio_running in PreH2.
    destruct restored.(SchedState).(isRunning); [reflexivity|].
    vm_compute in PreH2; discriminate. }
  unfold task_change_prio_post; rewrite Harguments.
  Exists cpu_sr acquired_execution acquired
    (task_change_priority_state sg acquired target_tid target_node oldprio destination)
    restored_execution restored.
  rewrite Hrunning; cbn [Z.eqb andb]; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_3 : OSTaskChangePrio_return_wit_3.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 0 X PreH2).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH13 ltac:(lia) PreH7) as Harguments.
  assert (Hrunning : restored.(SchedState).(isRunning) = false).
  { unfold task_change_prio_running in PreH1.
    destruct restored.(SchedState).(isRunning); [|reflexivity].
    exfalso; apply PreH1; vm_compute; reflexivity. }
  assert (Haddress : sg.(g_OSRunning) = &("OSRunning")).
  { unfold task_change_prio_addresses in PreH9; tauto. }
  rewrite <- Haddress.
  sep_apply (task_change_prio_closed_merge_running__return_contract
    environment saved_local critical sg restored_execution mask restored).
  unfold task_change_prio_post; rewrite Harguments.
  Exists cpu_sr acquired_execution acquired
    (task_change_priority_state sg acquired target_tid target_node oldprio destination)
    restored_execution restored.
  rewrite Hrunning; cbn [Z.eqb andb]; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_4 : OSTaskChangePrio_return_wit_4.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 0 X PreH2).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH13 ltac:(lia) PreH7) as Harguments.
  assert (Hrunning : restored.(SchedState).(isRunning) = false).
  { unfold task_change_prio_running in PreH1.
    destruct restored.(SchedState).(isRunning); [|reflexivity].
    exfalso; apply PreH1; vm_compute; reflexivity. }
  assert (Haddress : sg.(g_OSRunning) = &("OSRunning")).
  { unfold task_change_prio_addresses in PreH9; tauto. }
  rewrite <- Haddress.
  sep_apply (task_change_prio_closed_merge_running__return_contract
    environment saved_local critical sg restored_execution mask restored).
  unfold task_change_prio_post; rewrite Harguments.
  Exists cpu_sr acquired_execution acquired
    (task_change_priority_state sg acquired target_tid target_node oldprio destination)
    restored_execution restored.
  rewrite Hrunning; cbn [Z.eqb andb]; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_5 : OSTaskChangePrio_return_wit_5.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 67 X PreH4).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH15 ltac:(lia) PreH9) as Harguments.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    destination PreH15 PreH10 ltac:(lia) PreH22) as Hnew.
  pose proof (task_change_prio_table_reserved_is_reserved__return_contract sg acquired
    oldprio PreH10 ltac:(lia) PreH1) as Hold.
  destruct (task_change_prio_priority_constants__return_contract sg acquired PreH15)
    as [Hlowest _].
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 67);
    [exact Harguments|exact PreH13|exact PreH15|exact PreH15| |exact PreH14|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_TASK_NOT_EXIST; split; [|reflexivity].
  unfold task_change_prio_critical; rewrite Hnew; exists oldprio; split; [exact PreH19|].
  unfold task_change_prio_selected_effect; rewrite Hlowest.
  assert (Hidle : (oldprio =? 63) = false) by (apply Z.eqb_neq; exact PreH3).
  rewrite Hidle, Hold; auto.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_6 : OSTaskChangePrio_return_wit_6.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 67 X PreH4).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH15 ltac:(lia) PreH9) as Harguments.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    destination PreH15 PreH10 ltac:(lia) PreH22) as Hnew.
  pose proof (task_change_prio_table_reserved_is_reserved__return_contract sg acquired
    oldprio PreH10 ltac:(lia) PreH1) as Hold.
  destruct (task_change_prio_priority_constants__return_contract sg acquired PreH15)
    as [Hlowest _].
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 67);
    [exact Harguments|exact PreH13|exact PreH15|exact PreH15| |exact PreH14|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_TASK_NOT_EXIST; split; [|reflexivity].
  unfold task_change_prio_critical; rewrite Hnew; exists oldprio; split; [exact PreH19|].
  unfold task_change_prio_selected_effect; rewrite Hlowest.
  assert (Hidle : (oldprio =? 63) = false) by (apply Z.eqb_neq; exact PreH3).
  rewrite Hidle, Hold; auto.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_7 : OSTaskChangePrio_return_wit_7.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 41 X PreH3).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH14 ltac:(lia) PreH8) as Harguments.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    destination PreH14 PreH9 ltac:(lia) PreH21) as Hnew.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    oldprio PreH14 PreH9 ltac:(lia) PreH1) as Hold.
  destruct (task_change_prio_priority_constants__return_contract sg acquired PreH14)
    as [Hlowest _].
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 41);
    [exact Harguments|exact PreH12|exact PreH14|exact PreH14| |exact PreH13|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_PRIO; split; [|reflexivity].
  unfold task_change_prio_critical; rewrite Hnew; exists oldprio; split; [exact PreH18|].
  unfold task_change_prio_selected_effect; rewrite Hlowest.
  assert (Hidle : (oldprio =? 63) = false) by (apply Z.eqb_neq; exact PreH2).
  rewrite Hidle, Hold; auto.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_8 : OSTaskChangePrio_return_wit_8.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 41 X PreH3).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH14 ltac:(lia) PreH8) as Harguments.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    destination PreH14 PreH9 ltac:(lia) PreH21) as Hnew.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    oldprio PreH14 PreH9 ltac:(lia) PreH1) as Hold.
  destruct (task_change_prio_priority_constants__return_contract sg acquired PreH14)
    as [Hlowest _].
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 41);
    [exact Harguments|exact PreH12|exact PreH14|exact PreH14| |exact PreH13|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_PRIO; split; [|reflexivity].
  unfold task_change_prio_critical; rewrite Hnew; exists oldprio; split; [exact PreH18|].
  unfold task_change_prio_selected_effect; rewrite Hlowest.
  assert (Hidle : (oldprio =? 63) = false) by (apply Z.eqb_neq; exact PreH2).
  rewrite Hidle, Hold; auto.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_9 : OSTaskChangePrio_return_wit_9.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 42 X PreH2).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH13 ltac:(lia) PreH7) as Harguments.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    destination PreH13 PreH8 ltac:(lia) PreH20) as Hnew.
  destruct (task_change_prio_priority_constants__return_contract sg acquired PreH13)
    as [Hlowest _].
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 42);
    [exact Harguments|exact PreH11|exact PreH13|exact PreH13| |exact PreH12|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_PRIO_INVALID; split; [|reflexivity].
  apply task_change_prio_resolved_idle; [exact Hnew|].
  rewrite Hlowest, <- PreH1; exact PreH17.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_10 : OSTaskChangePrio_return_wit_10.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 42 X PreH2).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH13 ltac:(lia) PreH7) as Harguments.
  pose proof (task_change_prio_table_null_is_free__return_contract sg acquired
    destination PreH13 PreH8 ltac:(lia) PreH20) as Hnew.
  destruct (task_change_prio_priority_constants__return_contract sg acquired PreH13)
    as [Hlowest _].
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 42);
    [exact Harguments|exact PreH11|exact PreH13|exact PreH13| |exact PreH12|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_PRIO_INVALID; split; [|reflexivity].
  apply task_change_prio_resolved_idle; [exact Hnew|].
  rewrite Hlowest, <- PreH1; exact PreH17.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_11 : OSTaskChangePrio_return_wit_11.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 40 X PreH2).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH13 ltac:(lia) PreH7) as Harguments.
  assert (Hoccupied : acquired.(TskState).(prioTbl) destination <> PTFree).
  { rewrite task_change_prio_table_lookup__return_contract in PreH1 by lia.
    intro Hfree; rewrite Hfree in PreH1; apply PreH1; reflexivity. }
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 40);
    [exact Harguments|exact PreH11|exact PreH13|exact PreH13| |exact PreH12|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_PRIO_EXIST; split; [|reflexivity].
  apply task_change_prio_new_slot_occupied; auto.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_12 : OSTaskChangePrio_return_wit_12.
Proof.
  left; intros.
  sep_apply_r_atomic (task_change_prio_post_safe_return
    environment saved_local critical sg requested destination execution mask before 40 X PreH2).
  pose proof (task_change_prio_arguments_valid__return_contract sg acquired
    requested destination PreH13 ltac:(lia) PreH7) as Harguments.
  assert (Hoccupied : acquired.(TskState).(prioTbl) destination <> PTFree).
  { rewrite task_change_prio_table_lookup__return_contract in PreH1 by lia.
    intro Hfree; rewrite Hfree in PreH1; apply PreH1; reflexivity. }
  eapply (task_change_prio_error_restore_post__return_contract
    environment saved_local critical sg requested destination execution mask before
    cpu_sr acquired_execution acquired acquired 40);
    [exact Harguments|exact PreH11|exact PreH13|exact PreH13| |exact PreH12|lia].
  exists Ucos2Verify.lib.error_codes.OS_ERR_PRIO_EXIST; split; [|reflexivity].
  apply task_change_prio_new_slot_occupied; auto.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_13 : OSTaskChangePrio_return_wit_13.
Proof.
  unfold OSTaskChangePrio_return_wit_13; left; intros.
  sep_apply_l_atomic (task_change_prio_closed_implies_invariant__call_boundaries
    environment saved_local critical sg execution mask before).
  Intros.
  sep_apply_r_atomic (task_change_prio_post_error_safe_return
    environment saved_local critical sg requested destination execution mask before 42 X
    ltac:(lia) PreH14).
  unfold task_change_prio_post.
  rewrite (task_change_prio_argument_new_invalid__call_boundaries sg before requested destination)
    by (assumption || lia).
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_14 : OSTaskChangePrio_return_wit_14.
Proof.
  unfold OSTaskChangePrio_return_wit_14; left; intros.
  sep_apply_l_atomic (task_change_prio_closed_implies_invariant__call_boundaries
    environment saved_local critical sg execution mask before).
  Intros.
  sep_apply_r_atomic (task_change_prio_post_error_safe_return
    environment saved_local critical sg requested destination execution mask before 42 X
    ltac:(lia) PreH13).
  unfold task_change_prio_post.
  rewrite (task_change_prio_argument_new_invalid__call_boundaries sg before requested destination)
    by (assumption || lia).
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_return_wit_15 : OSTaskChangePrio_return_wit_15.
Proof.
  unfold OSTaskChangePrio_return_wit_15; left; intros.
  sep_apply_l_atomic (task_change_prio_closed_implies_invariant__call_boundaries
    environment saved_local critical sg execution mask before).
  Intros.
  sep_apply_r_atomic (task_change_prio_post_error_safe_return
    environment saved_local critical sg requested destination execution mask before 42 X
    ltac:(lia) PreH13).
  unfold task_change_prio_post.
  rewrite (task_change_prio_argument_old_invalid__call_boundaries sg before requested destination)
    by (assumption || lia).
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_partial_solve_wit_79_pure : OSTaskChangePrio_partial_solve_wit_79_pure.
Proof.
  left; intros.
  assert (Hrunning : task_change_prio_running restored = 1).
  { unfold task_change_prio_running in *.
    destruct (isRunning (SchedState restored)); [reflexivity|].
    cbv [unsigned_last_nbits] in PreH1; discriminate. }
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_partial_solve_wit_80_pure : OSTaskChangePrio_partial_solve_wit_80_pure.
Proof.
  left; intros.
  assert (Hrunning : task_change_prio_running restored = 1).
  { unfold task_change_prio_running in *.
    destruct (isRunning (SchedState restored)); [reflexivity|].
    cbv [unsigned_last_nbits] in PreH1; discriminate. }
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_1 : OSTaskChangePrio_which_implies_wit_1.
Proof.
  left; intros.
  destruct execution as [call|view];
    unfold task_change_prio_closed, os_sched_continuation_pre,
      kernel_continuation_call_closed, kernel_continuation_inv, kernel_program_inv;
    entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_2 : OSTaskChangePrio_which_implies_wit_2.
Proof.
  left; intros.
  pose proof (task_change_prio_table_split__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired) as Hsplit.
  destruct PreH1 as [Htable _]; rewrite Htable in Hsplit; exact Hsplit.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_3 : OSTaskChangePrio_which_implies_wit_3.
Proof.
  left; intros.
  pose proof (task_change_prio_table_merge__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired PreH2) as Hmerge.
  destruct PreH1 as [Htable _]; rewrite Htable in Hmerge; exact Hmerge.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_4 : OSTaskChangePrio_which_implies_wit_4.
Proof.
  left; intros.
  pose proof (task_change_prio_table_merge__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired PreH2) as Hmerge.
  destruct PreH1 as [Htable _]; rewrite Htable in Hmerge; exact Hmerge.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_5 : OSTaskChangePrio_which_implies_wit_5.
Proof.
  left; intros.
  pose proof (task_change_prio_profile_constants__task_state
    sg acquired PreH6) as [_ Hself].
  assert (Hfree : acquired.(TskState).(prioTbl) destination = PTFree).
  { eapply task_change_prio_table_zero_is_free__task_state;
      [exact PreH6|lia|exact PreH5]. }
  destruct (PreH7 ltac:(congruence) Hfree) as [tid [node Hcurrent]].
  pose proof (task_change_prio_self_split__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired
    tid node Hcurrent) as Hsplit.
  destruct PreH1 as [_ [Haddress _]].
  rewrite Haddress in Hsplit; cbn [tcb_field_address] in Hsplit.
  sep_apply Hsplit; Exists tid node; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_6 : OSTaskChangePrio_which_implies_wit_6.
Proof.
  left; intros.
  pose proof (task_change_prio_self_merge__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired
    current_tid current_node PreH2 PreH3) as Hmerge.
  destruct PreH1 as [_ [Haddress _]].
  rewrite Haddress in Hmerge; cbn [tcb_field_address] in Hmerge.
  exact Hmerge.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_7 : OSTaskChangePrio_which_implies_wit_7.
Proof.
  left; intros.
  pose proof (task_change_prio_table_split__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired) as Hsplit.
  destruct PreH1 as [Htable _]; rewrite Htable in Hsplit; exact Hsplit.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_8 : OSTaskChangePrio_which_implies_wit_8.
Proof.
  left; intros.
  pose proof (task_change_prio_table_merge__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired PreH2) as Hmerge.
  destruct PreH1 as [Htable _]; rewrite Htable in Hmerge; exact Hmerge.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_9 : OSTaskChangePrio_which_implies_wit_9.
Proof.
  left; intros.
  pose proof (task_change_prio_profile_constants__task_state
    sg acquired PreH2) as [Hlowest _].
  assert (Hfree : acquired.(TskState).(prioTbl) destination = PTFree).
  { eapply task_change_prio_table_zero_is_free__task_state;
      [exact PreH2|lia|exact PreH10]. }
  unfold task_change_prio_table in PreH11.
  rewrite prio_table_values_Znth in PreH11 by lia.
  destruct (acquired.(TskState).(prioTbl) oldprio) as [| |tid] eqn:Htable;
    cbn [prio_tbl_entry_to_addr] in PreH11; try contradiction.
  pose proof PreH2 as [_ [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Hslots _]] _].
  assert (Hrange : task_priority_in_range sg oldprio) by
    (unfold task_priority_in_range; lia).
  specialize (Hslots oldprio Hrange); rewrite Htable in Hslots.
  destruct Hslots as [node Hnode].
  assert (Howner : task_holds_no_mutex acquired.(EventState) tid).
  { eapply PreH5; [exact Hfree|exact PreH4|lia|exact Htable]. }
  pose proof (task_change_prio_live_selected_priority sg acquired tid node oldprio
    PreH2 Hnode Howner Hrange Htable) as Hpriority.
  assert (Hdistinct : oldprio <> destination) by
    (eapply task_change_prio_live_distinct_priority; eassumption).
  assert (Hlive : task_change_prio_live sg acquired requested oldprio destination tid node).
  { unfold task_change_prio_live; split; [exact PreH2|].
    split; [exact PreH4|]. split; [exact Hfree|]. split; [exact Htable|].
    split; [exact Hnode|]. split; [exact Howner|]. split; [exact Hpriority|].
    repeat split; lia. }
  assert (Hprange : 0 <= node.(curPrio) < 64) by lia.
  pose proof (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    node.(curPrio) Hprange) as [[Hx0 Hx8] [[Hy0 Hy8] _]].
  pose proof (task_change_prio_work_split__task_state
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired
    tid node PreH3 Hnode) as Hsplit.
  destruct PreH1 as [Haddress [_ [Hgroup [Hrows _]]]].
  rewrite Haddress, Hgroup, Hrows in Hsplit.
  cbn [tcb_field_address] in Hsplit.
  subst ptcb; sep_apply Hsplit; Exists node tid; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_10 : OSTaskChangePrio_which_implies_wit_10.
Proof.
  left; intros.
  pose proof (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    destination ltac:(lia)) as [[Hx0 Hx8] [[Hy0 Hy8] [Hx Hy]]].
  assert (Hshift : Z.shiftr destination 3 = tcb_y_of_prio destination).
  { rewrite Z.shiftr_div_pow2 by lia; reflexivity. }
  rewrite Hshift in PreH3.
  rewrite unsigned_last_nbits_eq in PreH3 by lia.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_11 : OSTaskChangePrio_which_implies_wit_11.
Proof.
  left; intros.
  destruct PreH2 as [Hinv [_ [_ [_ [Hnode [_ [Hold [Hrange _]]]]]]]].
  destruct Hinv as [Hprofile [_ [_ [Hevents [Hcross _]]]]].
  unfold task_change_prio_event_pointer in PreH3.
  destruct target_node.(eventPtr) as [eid|] eqn:Hptr; [|contradiction].
  destruct (cross_module_invariants.task_event_reference_has_waiter
    sg acquired target_tid target_node eid Hcross Hnode Hptr) as [e [Hget Hin]].
  pose proof (proj1 (event_pool_used_not_free sg acquired.(EventState) eid e
    (proj1 Hevents) Hget)) as Hvalid.
  destruct PreH1 as [Hconfig [Hlayout _]].
  destruct (proj2 (Hlayout eid Hvalid)) as [Hgroup Htable].
  unfold event_wait_fields_layout_prop, OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  assert (Hy : 0 <= tcb_y_of_prio target_node.(curPrio) < 8).
  { destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
      target_node.(curPrio) ltac:(lia)) as [_ [Hy _]]; exact Hy. }
  assert (Hbit : Z.land (Znth y_old (task_change_prio_event_rows acquired e) 0) bitx_old <> 0).
  { rewrite PreH5, PreH6, task_change_prio_event_rows_index__event_rows by assumption.
    eapply event_waiter_priority_bit_present__event_rows; eauto; lia. }
  sep_apply_l_atomic (event_raw_rep_split_eid sg acquired.(TskState) acquired.(EventState) eid e Hget).
  sep_apply_l_atomic (event_storage_split_bitmap__event_rows sg acquired.(TskState) eid e
    ltac:(rewrite Hconfig; reflexivity)).
  Exists e eid.
  rewrite PreH3, Hgroup, Htable.
  unfold task_change_prio_event_live, task_change_prio_event_frame,
    task_change_prio_event_rows, task_change_prio_event_group.
  entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_12 : OSTaskChangePrio_which_implies_wit_12.
Proof.
  left; intros.
  destruct PreH1 as [Hpointer Hget].
  destruct PreH3 as [_ [_ [_ [Hevents _]]]].
  pose proof (proj1 (event_pool_used_not_free sg acquired.(EventState)
    waiting_eid waiting_event (proj1 Hevents) Hget)) as Hvalid.
  destruct PreH2 as [_ [Hlayout _]].
  destruct (proj2 (Hlayout waiting_eid Hvalid)) as [Hgroup Htable].
  unfold event_wait_fields_layout_prop, OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  unfold task_change_prio_event_storage; rewrite Hpointer.
  Exists waiting_event.
  rewrite Hgroup, Htable; entailer!.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_13 : OSTaskChangePrio_which_implies_wit_13.
Proof.
  left; intros.
  pose proof (task_change_prio_work_frame_split_current
    environment saved_local critical sg acquired_execution cpu_sr acquired acquired
    target_tid target_node) as Hsplit.
  destruct PreH1 as [_ [Hcurrent [_ [_ [_ Hscheduler]]]]].
  destruct Hscheduler as [_ [_ [_ [Hpriority _]]]].
  rewrite Hcurrent, <- Hpriority in Hsplit; exact Hsplit.
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_14 : OSTaskChangePrio_which_implies_wit_14.
Proof.
  unfold OSTaskChangePrio_which_implies_wit_14; left; intros.
  destruct PreH1 as [_ [_ [_ [_ [Hrunning _]]]]].
  rewrite <- Hrunning.
  apply (proj1 (task_change_prio_closed_split_running__call_boundaries
    environment saved_local critical sg restored_execution mask restored)).
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_15 : OSTaskChangePrio_which_implies_wit_15.
Proof.
  unfold OSTaskChangePrio_which_implies_wit_15; left; intros.
  destruct PreH1 as [_ [_ [_ [_ [Hrunning _]]]]].
  rewrite <- Hrunning.
  apply (proj2 (task_change_prio_closed_split_running__call_boundaries
    environment saved_local critical sg restored_execution mask restored)).
Qed. 

Lemma proof_of_OSTaskChangePrio_which_implies_wit_16 : OSTaskChangePrio_which_implies_wit_16.
Proof.
  unfold OSTaskChangePrio_which_implies_wit_16; left; intros.
  assert (Hrunning : restored.(SchedState).(isRunning) = true).
  { unfold task_change_prio_running in PreH4.
    destruct restored.(SchedState).(isRunning); [reflexivity|discriminate]. }
  eapply task_change_prio_closed_implies_scheduler_pre__call_boundaries; eassumption.
Qed. 

