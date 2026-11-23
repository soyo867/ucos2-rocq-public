From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.micromega.Lia.
From Ucos2Verify.VC.code.sched Require Import tmr_task_unlock_entry_goal.
From Ucos2Verify.VC.code.sched Require Import tmr_task_unlock_entry_proof_auto.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_call_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_signal_return_spec.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_unlock_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_status_callback_spec.

Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_scheduler_entry_spec.

Lemma proof_of_OSSchedUnlock_return_wit_5 : tmr_task_unlock_entry_goal.OSSchedUnlock_return_wit_5.
Proof.
  left; intros.
  pose proof PreH2 as [Hrunning _]; rewrite Hrunning.
  apply tmr_task_unlock_fields_not_running_entry_return.
  - split; [exact (proj1 PreH6)|exact PreH4].
  - exact PreH5.
  - intro Heq; apply PreH1; rewrite Heq; reflexivity.
  - exact PreH7.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_4_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_4_pure.
Proof.
  left; intros.
  assert (Hrunning : os_sched_unlock_running before = 1).
  { unfold os_sched_unlock_running in PreH6 |- *.
    destruct (isRunning (SchedState before)); [reflexivity|discriminate PreH6]. }
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_5_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_5_pure.
Proof.
  left; intros.
  pose proof (os_sched_unlock_positive_counted_locks acquired PreH3 ltac:(lia)) as Hcount.
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_7_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_7_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [_ [Hready _]]]].
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_9_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_9_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [_ [Hready [Hlayout _]]]]].
  assert (Hrequest : os_sched_unlock_requests acquired = true).
  { apply (proj2 (os_sched_unlock_positive_requests_after_decrement acquired PreH20 ltac:(lia))).
    rewrite (os_sched_unlock_positive_counted_locks acquired PreH20 ltac:(lia)).
    exact PreH18. }
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_10_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_10_pure.
Proof.
  left; intros.
  pose proof PreH1 as [_ Haddresses].
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_11_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_11_pure.
Proof.
  left; intros.
  pose proof PreH6 as [_ [_ [Hsafe _]]].
  assert (Hrequest : os_sched_unlock_requests acquired = true).
  { apply (proj2 (os_sched_unlock_positive_requests_after_decrement acquired PreH28 ltac:(lia))).
    rewrite (os_sched_unlock_positive_counted_locks acquired PreH28 ltac:(lia)).
    exact PreH26. }
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_12_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_12_pure.
Proof.
  left; intros.
  pose proof (os_sched_unlock_positive_counted_locks acquired PreH3 ltac:(lia)) as Hcount.
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_14_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_14_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [_ [Hready _]]]].
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_15_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_15_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [Hsafe _]]].
  assert (Hrequest : os_sched_unlock_requests acquired = false).
  { destruct (os_sched_unlock_requests acquired) eqn:Hrequest; [|reflexivity].
    pose proof (proj1 (os_sched_unlock_positive_requests_after_decrement acquired PreH14 ltac:(lia)) Hrequest) as Hzero.
    rewrite (os_sched_unlock_positive_counted_locks acquired PreH14 ltac:(lia)) in Hzero.
    contradiction. }
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_16_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_16_pure.
Proof.
  left; intros.
  assert (Hzero : os_sched_locks acquired = 0) by lia.
  pose proof (os_sched_unlock_zero_count acquired Hzero) as [Hcount _].
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_18_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_18_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [_ [Hready _]]]].
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_19_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_19_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [Hsafe _]]].
  assert (Hzero : os_sched_locks acquired = 0) by lia.
  pose proof (os_sched_unlock_zero_count acquired Hzero) as [_ Hrequest].
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_20_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_20_pure.
Proof.
  left; intros.
  pose proof (os_sched_unlock_isr_count acquired PreH1) as [Hcount _].
  entailer!; lia.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_22_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_22_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [_ [Hready _]]]].
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_partial_solve_wit_23_pure : tmr_task_unlock_entry_goal.OSSchedUnlock_partial_solve_wit_23_pure.
Proof.
  left; intros.
  pose proof PreH5 as [_ [_ [Hsafe _]]].
  pose proof (os_sched_unlock_isr_count acquired PreH12) as [_ Hrequest].
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_1 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_1.
Proof.
  right; intros.
  pose proof PreH1 as [Hrunning _].
  sep_apply_l_atomic (tmr_task_unlock_fields_pre_open environment critical local sg context mask before X).
  apply coq_prop_andp_left; intros [Hentry [Hclients [Hsafe [Hready [Hlayout Hvalid]]]]].
  rewrite <- Hrunning.
  unfold tmr_task_unlock_call_facts; entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_2 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_2.
Proof.
  right; intros.
  pose proof PreH1 as [Hrunning _]; rewrite Hrunning.
  exact (proj2 (os_sched_fields_split_running environment local sg context mask before)).
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_3 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_3.
Proof.
  left; intros.
  pose proof PreH1 as [Hrunning [Hints [Hlocks Hrest]]].
  sep_apply_l_atomic (os_sched_unlock_fields_save_counters environment critical local
    sg context mask cpu_sr before PreH6 PreH7).
  Intros entered acquired.
  try (apply coq_prop_andp_left; intro).
  lazymatch goal with
  | Hfacts : os_sched_unlock_continuation_saved_facts environment critical sg context
      mask cpu_sr before entered acquired /\
      0 <= os_sched_ints acquired <= 255 /\ 0 <= os_sched_locks acquired <= 255 |- _ =>
      destruct Hfacts as [Hsaved [[Hint_lower Hint_upper] [Hlock_lower Hlock_upper]]]
  end.
  Exists entered acquired; rewrite <- Hints, <- Hlocks; entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_4 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_4.
Proof.
  right; intros.
  pose proof PreH1 as [Hrunning [Hints [Hlocks Hrest]]].
  rewrite Hints, Hlocks.
  apply os_sched_unlock_fields_merge_counters;
    unfold os_sched_unlock_continuation_saved_facts, os_sched_lock_continuation_saved_facts in PreH6;
    tauto.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_5 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_5.
Proof.
  right; intros.
  apply os_sched_unlock_fields_restore_return; assumption.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_6 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_6.
Proof.
  left; intros.
  unfold os_sched_unlock_fields_restored_post.
  Intros restored unlocked.
  Exists restored unlocked; entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_7 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_7.
Proof.
  right; intros.
  pose proof PreH5 as [_ [_ [_ [_ [_ Hvalid]]]]].
  pose proof PreH6 as [_ Hsources].
  pose proof (tmr_task_unlock_fields_prefix_preserves_signal_lifetime environment critical sg context
    mask before acquired restored unlocked Hvalid PreH4 Hsources) as Hlife.
  apply UCOS2_C_Rules._derivable1_andp_intros.
  - apply derivable1s_coq_prop_r; exact Hlife.
  - eapply (tmr_task_unlock_fields_scheduler_entry_pre environment critical local
      sg context mask before acquired restored unlocked X); eassumption.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_8 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_8.
Proof.
  right; intros.
  pose proof (proj1 PreH5) as Hentry.
  eapply tmr_task_unlock_fields_scheduled_entry_return; eassumption.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_9 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_9.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_4.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_10 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_10.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_5.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_11 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_11.
Proof.
  right; intros.
  pose proof PreH5 as [Hentry [_ [_ [_ [_ Hvalid]]]]].
  eapply tmr_task_unlock_fields_no_schedule_entry_return; try eassumption.
  split; [exact Hentry|exact PreH3].
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_12 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_12.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_4.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_13 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_13.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_5.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_14 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_14.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_11.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_15 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_15.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_4.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_16 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_16.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_5.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_17 : tmr_task_unlock_entry_goal.OSSchedUnlock_which_implies_wit_17.
Proof.
  exact proof_of_OSSchedUnlock_which_implies_wit_11.
Qed.
