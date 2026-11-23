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
From Ucos2Verify.VC.code.interrupt Require Import int_exit_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSIntExit_entail_wit_1_1 : OSIntExit_entail_wit_1_1.
Proof.
  right; intros.
  assert (Hpositive : (0 <? entry_3.(IntrState).(intNesting)) = true).
  { apply Z.ltb_lt. unfold os_sched_ints in PreH1; lia. }
  unfold os_int_exit_counted_ints, os_int_exit_after_nesting, interrupt_exit_state.
  cbn [replace_IntrS IntrState]. rewrite Hpositive.
  cbn [intNesting]. unfold os_sched_ints; entailer!.
Qed.

Lemma proof_of_OSIntExit_entail_wit_1_2 : OSIntExit_entail_wit_1_2.
Proof.
  right; intros.
  assert (Hnonpositive : (0 <? entry_3.(IntrState).(intNesting)) = false).
  { apply Z.ltb_ge. unfold os_sched_ints in PreH1; lia. }
  unfold os_int_exit_counted_ints, os_int_exit_after_nesting, interrupt_exit_state.
  cbn [replace_IntrS IntrState]. rewrite Hnonpositive.
  unfold os_sched_ints; entailer!.
Qed.

Lemma proof_of_OSIntExit_entail_wit_2 : OSIntExit_entail_wit_2.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range (&( "OSIntNesting" )) (os_int_exit_counted_ints entry_2)).
  prop_apply_p (store_uchar_range (&( "OSLockNesting" )) (os_sched_locks entry_2)).
  Intros.
  change (0 <= os_int_exit_counted_ints entry_2 <= 255) in H.
  change (0 <= os_sched_locks entry_2 <= 255) in H0.
  assert (Hcounted : os_int_exit_counted_ints entry_2 = 0).
  { rewrite (unsigned_last_nbits_eq _ 32) in PreH3.
    - exact PreH3.
    - change (0 <= os_int_exit_counted_ints entry_2 < 4294967296); lia. }
  assert (Hlocked : os_sched_locks entry_2 = 0).
  { rewrite (unsigned_last_nbits_eq _ 32) in PreH2.
    - exact PreH2.
    - change (0 <= os_sched_locks entry_2 < 4294967296); lia. }
  pose proof (sched_new_priority_in_range (os_sched_group entry_2) (os_sched_rows entry_2)) as Hpriority.
  rewrite <- os_sched_selected_eq_callee_result in Hpriority.
  pose proof PreH7 as [Hrunning [Hints [Hlocks [Hhigh Haddresses]]]].
  Exists entry_2.
  rewrite <- os_sched_selected_eq_callee_result.
  rewrite os_int_exit_sched_new_split_high.
  rewrite Hhigh.
  entailer!.
  rewrite <- Hhigh; exact PreH7.
Qed.

Lemma proof_of_OSIntExit_entail_wit_3 : OSIntExit_entail_wit_3.
Proof.
  left; intros.
  pose proof PreH3 as [_ [_ [Hvalid [_ [Hnonempty Hswitch_input]]]]].
  pose proof PreH6 as [Hrunning [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter Hnew]]]]]]]].
  assert (Hlocks_after : os_sched_locks (os_int_exit_after_nesting entry_2) = os_sched_locks entry_2).
  { unfold os_sched_locks, os_int_exit_after_nesting, interrupt_exit_state.
    cbn [replace_IntrS IntrState].
    destruct (0 <? entry_2.(IntrState).(intNesting)); reflexivity. }
  assert (Hwork_frame : os_sched_work_frame sg (os_int_exit_after_nesting entry_2) =
    os_sched_work_frame sg entry_2) by reflexivity.
  assert (Hselection : os_sched_selection_enabled (os_int_exit_after_nesting entry_2) = true).
  { unfold os_sched_selection_enabled.
    change ((os_int_exit_counted_ints entry_2 =? 0) &&
      (os_sched_locks (os_int_exit_after_nesting entry_2) =? 0) = true)%bool.
    rewrite Hlocks_after, PreH4, PreH5; reflexivity. }
  assert (Hrequest : os_sched_requests_switch (os_int_exit_after_nesting entry_2) = true).
  { unfold os_sched_requests_switch; rewrite Hselection.
    change (sched_switch_byte_guard (os_sched_selected entry_2) (os_sched_current entry_2) = true).
    unfold sched_switch_byte_guard.
    apply Bool.negb_true_iff; apply Z.eqb_neq; exact PreH1. }
  assert (Hinput : os_int_exit_switch_input external port sg context entry_2).
  { apply Hswitch_input; exact Hrequest. }
  Exists entry_2.
  sep_apply_r_atomic (os_int_exit_body_transfer_program_pre
    external platform port critical sg context mask cpu_sr before entry_2 X PreH3 PreH2).
  unfold os_int_exit_transfer_pre.
  rewrite Hints, Hlocks, Hhigh, Hcurrent, Hpointer, Htable, Hcounter.
  rewrite os_sched_selected_table_value.
  entailer!.
  sep_apply_r_atomic (os_int_exit_prefix_cells_merge sg entry_2 Hvalid Hnonempty).
  unfold os_int_exit_prefix_cells, os_sched_work_cells.
  rewrite Hselection, Hrequest, Hlocks_after, Hwork_frame.
  change (os_sched_ints (os_int_exit_after_nesting entry_2)) with (os_int_exit_counted_ints entry_2).
  change (os_sched_group (os_int_exit_after_nesting entry_2)) with (os_sched_group entry_2).
  change (os_sched_rows (os_int_exit_after_nesting entry_2)) with (os_sched_rows entry_2).
  change (os_sched_selected (os_int_exit_after_nesting entry_2)) with (os_sched_selected entry_2).
  change (os_sched_selected_tcb sg (os_int_exit_after_nesting entry_2)) with (os_sched_selected_tcb sg entry_2).
  change (os_sched_table sg (os_int_exit_after_nesting entry_2)) with (os_sched_table sg entry_2).
  change (os_sched_current (os_int_exit_after_nesting entry_2)) with (os_sched_current entry_2).
  change (os_sched_counter (os_int_exit_after_nesting entry_2)) with (os_sched_counter entry_2).
  change (os_sched_old_high (os_int_exit_after_nesting entry_2)) with (os_sched_old_high entry_2).
  change (os_sched_old_pointer sg (os_int_exit_after_nesting entry_2)) with (os_sched_old_pointer sg entry_2).
  unfold os_int_exit_ready_tables, sched_new_rep, unsigned_last_nbits.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_entail_wit_4_1 : OSIntExit_entail_wit_4_1.
Proof.
  left; intros.
  pose proof PreH3 as [_ [_ [Hvalid [_ [Hnonempty Hswitch_input]]]]].
  pose proof PreH6 as [Hrunning [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter Hnew]]]]]]]].
  assert (Hlocks_after : os_sched_locks (os_int_exit_after_nesting entry_2) = os_sched_locks entry_2).
  { unfold os_sched_locks, os_int_exit_after_nesting, interrupt_exit_state.
    cbn [replace_IntrS IntrState].
    destruct (0 <? entry_2.(IntrState).(intNesting)); reflexivity. }
  assert (Hwork_frame : os_sched_work_frame sg (os_int_exit_after_nesting entry_2) =
    os_sched_work_frame sg entry_2) by reflexivity.
  assert (Hselection : os_sched_selection_enabled (os_int_exit_after_nesting entry_2) = true).
  { unfold os_sched_selection_enabled.
    change ((os_int_exit_counted_ints entry_2 =? 0) &&
      (os_sched_locks (os_int_exit_after_nesting entry_2) =? 0) = true)%bool.
    rewrite Hlocks_after, PreH4, PreH5; reflexivity. }
  assert (Hrequest : os_sched_requests_switch (os_int_exit_after_nesting entry_2) = false).
  { unfold os_sched_requests_switch; rewrite Hselection.
    change (sched_switch_byte_guard (os_sched_selected entry_2) (os_sched_current entry_2) = false).
    unfold sched_switch_byte_guard.
    rewrite PreH1, Z.eqb_refl; reflexivity. }
  Exists entry_2.
  rewrite Hints, Hlocks, Hhigh, Hcurrent, Hpointer, Htable, Hcounter.
  rewrite os_sched_selected_table_value.
  entailer!.
  sep_apply_r_atomic (os_int_exit_prefix_cells_merge sg entry_2 Hvalid Hnonempty).
  unfold os_int_exit_prefix_cells, os_sched_work_cells.
  rewrite Hselection, Hrequest, Hlocks_after, Hwork_frame.
  change (os_sched_ints (os_int_exit_after_nesting entry_2)) with (os_int_exit_counted_ints entry_2).
  change (os_sched_group (os_int_exit_after_nesting entry_2)) with (os_sched_group entry_2).
  change (os_sched_rows (os_int_exit_after_nesting entry_2)) with (os_sched_rows entry_2).
  change (os_sched_selected (os_int_exit_after_nesting entry_2)) with (os_sched_selected entry_2).
  change (os_sched_selected_tcb sg (os_int_exit_after_nesting entry_2)) with (os_sched_selected_tcb sg entry_2).
  change (os_sched_table sg (os_int_exit_after_nesting entry_2)) with (os_sched_table sg entry_2).
  change (os_sched_current (os_int_exit_after_nesting entry_2)) with (os_sched_current entry_2).
  change (os_sched_counter (os_int_exit_after_nesting entry_2)) with (os_sched_counter entry_2).
  change (os_sched_old_high (os_int_exit_after_nesting entry_2)) with (os_sched_old_high entry_2).
  change (os_sched_old_pointer sg (os_int_exit_after_nesting entry_2)) with (os_sched_old_pointer sg entry_2).
  unfold os_int_exit_ready_tables, sched_new_rep.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_entail_wit_4_2 : OSIntExit_entail_wit_4_2.
Proof.
  left; intros.
  pose proof PreH4 as [_ [_ [Hvalid [_ [Hnonempty Hswitch_input]]]]].
  pose proof PreH6 as [Hrunning [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter Hnew]]]]]]]].
  assert (Hlocks_after : os_sched_locks (os_int_exit_after_nesting entry_2) = os_sched_locks entry_2).
  { unfold os_sched_locks, os_int_exit_after_nesting, interrupt_exit_state.
    cbn [replace_IntrS IntrState].
    destruct (0 <? entry_2.(IntrState).(intNesting)); reflexivity. }
  assert (Hwork_frame : os_sched_work_frame sg (os_int_exit_after_nesting entry_2) =
    os_sched_work_frame sg entry_2) by reflexivity.
  assert (Hnonzero : os_sched_locks entry_2 <> 0).
  { intro Hzero; apply PreH1; rewrite Hzero; reflexivity. }
  assert (Hselection : os_sched_selection_enabled (os_int_exit_after_nesting entry_2) = false).
  { unfold os_sched_selection_enabled.
    change ((os_int_exit_counted_ints entry_2 =? 0) &&
      (os_sched_locks (os_int_exit_after_nesting entry_2) =? 0) = false)%bool.
    rewrite Hlocks_after.
    apply Bool.andb_false_iff; right; apply Z.eqb_neq; exact Hnonzero. }
  assert (Hrequest : os_sched_requests_switch (os_int_exit_after_nesting entry_2) = false).
  { unfold os_sched_requests_switch; rewrite Hselection; reflexivity. }
  Exists entry_2.
  rewrite Hints, Hlocks, Hcurrent, Hpointer, Htable, Hcounter.
  
  entailer!.
  sep_apply_r_atomic (os_int_exit_prefix_cells_merge sg entry_2 Hvalid Hnonempty).
  unfold os_int_exit_prefix_cells, os_sched_work_cells.
  rewrite Hselection, Hrequest, Hlocks_after, Hwork_frame.
  change (os_sched_ints (os_int_exit_after_nesting entry_2)) with (os_int_exit_counted_ints entry_2).
  change (os_sched_group (os_int_exit_after_nesting entry_2)) with (os_sched_group entry_2).
  change (os_sched_rows (os_int_exit_after_nesting entry_2)) with (os_sched_rows entry_2).
  change (os_sched_selected (os_int_exit_after_nesting entry_2)) with (os_sched_selected entry_2).
  change (os_sched_selected_tcb sg (os_int_exit_after_nesting entry_2)) with (os_sched_selected_tcb sg entry_2).
  change (os_sched_table sg (os_int_exit_after_nesting entry_2)) with (os_sched_table sg entry_2).
  change (os_sched_current (os_int_exit_after_nesting entry_2)) with (os_sched_current entry_2).
  change (os_sched_counter (os_int_exit_after_nesting entry_2)) with (os_sched_counter entry_2).
  change (os_sched_old_high (os_int_exit_after_nesting entry_2)) with (os_sched_old_high entry_2).
  change (os_sched_old_pointer sg (os_int_exit_after_nesting entry_2)) with (os_sched_old_pointer sg entry_2).
  unfold os_int_exit_ready_tables, sched_new_rep.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_entail_wit_4_3 : OSIntExit_entail_wit_4_3.
Proof.
  left; intros.
  pose proof PreH3 as [_ [_ [Hvalid [_ [Hnonempty Hswitch_input]]]]].
  pose proof PreH5 as [Hrunning [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter Hnew]]]]]]]].
  assert (Hlocks_after : os_sched_locks (os_int_exit_after_nesting entry_2) = os_sched_locks entry_2).
  { unfold os_sched_locks, os_int_exit_after_nesting, interrupt_exit_state.
    cbn [replace_IntrS IntrState].
    destruct (0 <? entry_2.(IntrState).(intNesting)); reflexivity. }
  assert (Hwork_frame : os_sched_work_frame sg (os_int_exit_after_nesting entry_2) =
    os_sched_work_frame sg entry_2) by reflexivity.
  assert (Hnonzero : os_int_exit_counted_ints entry_2 <> 0).
  { intro Hzero; apply PreH1; rewrite Hzero; reflexivity. }
  assert (Hselection : os_sched_selection_enabled (os_int_exit_after_nesting entry_2) = false).
  { unfold os_sched_selection_enabled.
    change ((os_int_exit_counted_ints entry_2 =? 0) &&
      (os_sched_locks (os_int_exit_after_nesting entry_2) =? 0) = false)%bool.
    rewrite Hlocks_after.
    apply Bool.andb_false_iff; left; apply Z.eqb_neq; exact Hnonzero. }
  assert (Hrequest : os_sched_requests_switch (os_int_exit_after_nesting entry_2) = false).
  { unfold os_sched_requests_switch; rewrite Hselection; reflexivity. }
  Exists entry_2.
  rewrite Hints, Hlocks, Hcurrent, Hpointer, Htable, Hcounter.
  
  entailer!.
  sep_apply_r_atomic (os_int_exit_prefix_cells_merge sg entry_2 Hvalid Hnonempty).
  unfold os_int_exit_prefix_cells, os_sched_work_cells.
  rewrite Hselection, Hrequest, Hlocks_after, Hwork_frame.
  change (os_sched_ints (os_int_exit_after_nesting entry_2)) with (os_int_exit_counted_ints entry_2).
  change (os_sched_group (os_int_exit_after_nesting entry_2)) with (os_sched_group entry_2).
  change (os_sched_rows (os_int_exit_after_nesting entry_2)) with (os_sched_rows entry_2).
  change (os_sched_selected (os_int_exit_after_nesting entry_2)) with (os_sched_selected entry_2).
  change (os_sched_selected_tcb sg (os_int_exit_after_nesting entry_2)) with (os_sched_selected_tcb sg entry_2).
  change (os_sched_table sg (os_int_exit_after_nesting entry_2)) with (os_sched_table sg entry_2).
  change (os_sched_current (os_int_exit_after_nesting entry_2)) with (os_sched_current entry_2).
  change (os_sched_counter (os_int_exit_after_nesting entry_2)) with (os_sched_counter entry_2).
  change (os_sched_old_high (os_int_exit_after_nesting entry_2)) with (os_sched_old_high entry_2).
  change (os_sched_old_pointer sg (os_int_exit_after_nesting entry_2)) with (os_sched_old_pointer sg entry_2).
  unfold os_int_exit_ready_tables, sched_new_rep.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_return_wit_1 : OSIntExit_return_wit_1.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_int_exit_continuation external port critical sg context before X |- _ =>
      sep_apply_l_atomic (os_int_exit_post_program_post external platform port critical
        sg context mask before X Hsafe)
  end.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_return_wit_2 : OSIntExit_return_wit_2.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_int_exit_continuation external port critical sg context before X |- _ =>
      sep_apply_r_atomic (os_int_exit_post_program_post external platform port critical
        sg context mask before X Hsafe)
  end.
  pose proof PreH6 as [Hrunning Haddresses].
  assert (Hnotrunning : os_int_exit_running before <> 1).
  { intro Hvalue; apply PreH1; rewrite Hvalue; reflexivity. }
  rewrite Hrunning.
  apply os_int_exit_not_running_return; assumption.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_2_pure : OSIntExit_partial_solve_wit_2_pure.
Proof.
  left; intros.
  assert (Hrunning : os_int_exit_running before = 1).
  { unfold os_int_exit_running in PreH1 |- *.
    destruct before.(SchedState).(isRunning); [reflexivity|discriminate PreH1]. }
  entailer!.
Qed.

Lemma proof_of_OSIntExit_which_implies_wit_1 : OSIntExit_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH1 as [Hrunning Haddresses].
  unfold os_sched_global_addresses in Haddresses.
  destruct Haddresses as [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter Hnew]]]]]]].
  unfold os_int_exit_program_pre, os_int_exit_pre. rewrite Hrunning; entailer!.
  rewrite <- Hrunning; exact PreH1.
Qed.

Lemma proof_of_OSIntExit_which_implies_wit_2 : OSIntExit_which_implies_wit_2.
Proof.
  left; intros.
  pose proof PreH4 as [Hrunning [Hints [Hlocks [Hhigh [Hcurrent [Hpointer [Htable [Hcounter Hnew]]]]]]]].
  Exists entry_2.
  unfold os_sched_work_cells.
  rewrite Hints, Hlocks, Hcurrent, Hpointer, Htable, Hcounter.
  prop_apply (store_uchar_range sg.(g_OSIntNesting) (os_sched_ints entry_2)).
  Intros. entailer!.
  rewrite <- Hints, <- Hlocks, <- Hcurrent, <- Hpointer, <- Htable, <- Hcounter; exact PreH4.
Qed.
