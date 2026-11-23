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
From Ucos2Verify.VC.code.queue Require Import q_post_front_goal.
From Ucos2Verify.VC.code.queue Require Import q_post_front_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.queue.spec.q_post_front_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSQPostFront_entail_wit_1 : OSQPostFront_entail_wit_1.
Proof.
  left; intros; unfold store_uchar; entailer!.
Qed.

Lemma proof_of_OSQPostFront_entail_wit_2 : OSQPostFront_entail_wit_2.
Proof.
  left; intros.
  subst pmsg_pre pevent_pre pe.
  Exists retval_2 active_2 acquired_3 current_3 tid_2 old_2.
  entailer!.
Qed.

Lemma proof_of_OSQPostFront_entail_wit_3_1 : OSQPostFront_entail_wit_3_1.
Proof.
  left; intros.
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_4.
  assert (Hnext : q_post_front_next_out q_4 = q_post_front_wrapped_out q_4 - sizeof(PTR))
    by reflexivity.
  assert (Hwrap : q_post_front_wrapped_out q_4 = queue_end_addr q_4).
  { unfold q_post_front_wrapped_out; rewrite (proj2 (Z.eqb_eq _ _) PreH1); reflexivity. }
  rewrite Hwrap in Hnext |- *.
  entailer!.
  rewrite PreH12, PreH29; entailer!.
Qed.

Lemma proof_of_OSQPostFront_entail_wit_3_2 : OSQPostFront_entail_wit_3_2.
Proof.
  left; intros.
  Exists active_2 acquired_3 current_3 free_2 slots_2 q_4.
  assert (Hnext : q_post_front_next_out q_4 = q_post_front_wrapped_out q_4 - sizeof(PTR))
    by reflexivity.
  assert (Hwrap : q_post_front_wrapped_out q_4 = queue_out_addr q_4).
  { unfold q_post_front_wrapped_out; rewrite (proj2 (Z.eqb_neq _ _) PreH1); reflexivity. }
  rewrite Hwrap in Hnext |- *.
  entailer!.
  rewrite PreH12, PreH29; entailer!.
Qed.

Lemma proof_of_OSQPostFront_entail_wit_4 : OSQPostFront_entail_wit_4.
Proof.
  left; intros.
  Exists active_2 acquired_2 current_2 free_2 slots_2 q_2.
  replace (q_post_front_wrapped_out q_2 + -1 * sizeof(PTR))
    with (q_post_front_next_out q_2) by lia.
  entailer!.
Qed.

Lemma proof_of_OSQPostFront_entail_wit_5 : OSQPostFront_entail_wit_5.
Proof.
  left; intros.
  unfold q_post_front_slot_frame; Intros.
  Exists active_2 acquired_2 current_2 free_2 slots_2 q_2.
  entailer!.
Qed.

Lemma proof_of_OSQPostFront_return_wit_1 : OSQPostFront_return_wit_1.
Proof.
  left; intros; apply q_post_front_nonschedule_return; assumption.
Qed.

Lemma proof_of_OSQPostFront_return_wit_2 : OSQPostFront_return_wit_2.
Proof.
  left; intros; subst pe.
  apply q_post_front_nonschedule_return; assumption.
Qed.

Lemma proof_of_OSQPostFront_return_wit_3 : OSQPostFront_return_wit_3.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  eapply q_post_front_sched_return; eassumption.
Qed.

Lemma proof_of_OSQPostFront_return_wit_4 : OSQPostFront_return_wit_4.
Proof.
  left; intros.
  assert (Hresult : q_post_front_caller_result environment critical sg caller mask
    pe eid message before 1 caller before).
  { exists caller, before, false; split; [|auto].
    unfold q_post_front_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) PreH7),
      (proj2 (Z.eqb_neq _ _) PreH1); auto. }
  sep_apply_r_atomic (q_post_front_closed_return environment critical saved_local
    sg caller caller mask pe eid message before before 1 X Hresult PreH19).
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH10).
  pose proof ((proj1 (proj2 PreH9)) eid PreH8) as [[Htype _] _].
  rewrite PreH6, Htype; unfold q_post_type_context.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH10).
  entailer!.
Qed.

Lemma proof_of_OSQPostFront_return_wit_5 : OSQPostFront_return_wit_5.
Proof.
  left; intros; subst pevent_pre pe.
  apply q_post_front_closed_return; [|assumption].
  exists caller, before, false; split; [|auto].
  unfold q_post_front_prefix_program; cbn; auto.
Qed.

Lemma proof_of_OSQPostFront_partial_solve_wit_5_pure : OSQPostFront_partial_solve_wit_5_pure.
Proof.
  left; intros.
  assert (Hgroup : q_post_group acquired current <> 0).
  { intro Hz; rewrite Hz in PreH1; apply PreH1; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSQPostFront_partial_solve_wit_6_pure : OSQPostFront_partial_solve_wit_6_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH26.
  entailer!; tauto.
Qed.

Lemma proof_of_OSQPostFront_partial_solve_wit_11_pure : OSQPostFront_partial_solve_wit_11_pure.
Proof.
  left; intros.
  sep_apply_l_atomic (store_uchar_range
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (q_post_group acquired current)).
  Intros.
  assert (Hcast : unsigned_last_nbits (q_post_group acquired current) 32 =
    q_post_group acquired current).
  { apply unsigned_last_nbits_eq; cbn in *; lia. }
  rewrite Hcast in PreH1; entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_1 : OSQPostFront_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH4 as [Hzero|[Hnonzero [Haddress [Hid [Hslot Hprotocol]]]]];
    [contradiction|].
  pose proof ((proj1 (proj2 PreH2)) eid Hid) as [[Htype _] _].
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH3).
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  rewrite Haddress, Htype; unfold q_post_type_context; entailer!.
  rewrite <- Haddress; exact PreH4.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_2 : OSQPostFront_which_implies_wit_2.
Proof.
  left; intros; unfold q_post_save_pre.
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH5).
  pose proof ((proj1 (proj2 PreH4)) eid PreH3) as [[Htype _] _].
  rewrite PreH1, Htype; unfold q_post_type_context.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH5).
  entailer!.
  rewrite <- PreH1; exact PreH6.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_3 : OSQPostFront_which_implies_wit_3.
Proof.
  left; intros; subst pevent.
  unfold q_post_save_result; Intros active acquired current.
  pose proof H as [Hsave [Hbefore [Htype [Hlookup [Hcurrent Hgeneration]]]]].
  pose proof PreH3 as [_ [Hlayout _]].
  specialize (Hlayout eid PreH2).
  pose proof Hlayout as [_ [Hgroup_addr Htable_addr]].
  rewrite q_post_masked_equiv.
  sep_apply_l_atomic (q_post_group_cell_split sg acquired eid current Hlookup).
  Intros.
  Exists active acquired current.
  unfold q_post_group_context; rewrite Hgroup_addr; entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_4 : OSQPostFront_which_implies_wit_4.
Proof.
  left; intros; subst pevent.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Hid]].
  pose proof Hacquire as [Hsave [Hbefore [Htype [Hlookup [Hcurrent Hgeneration]]]]].
  pose proof Hsave as [Hvalid Hrest].
  pose proof Hprofile as [_ [Hlayout _]].
  specialize (Hlayout eid Hid).
  pose proof Hlayout as [_ [Hgroup_addr Htable_addr]].
  rewrite Hgroup_addr.
  sep_apply_l_atomic (q_post_group_cell_merge sg acquired_2 eid current_2 Hvalid Hlookup).
  sep_apply_l_atomic (q_post_wake_split sg acquired_2 eid current_2
    Hvalid Hlookup Hcurrent PreH2 Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 current_2 tid old.
  unfold q_post_wake_context, q_post_sched_group, q_post_sched_rows; entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_5 : OSQPostFront_which_implies_wit_5.
Proof.
  left; intros.
  unfold q_post_wake_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid [Hgroup Hentry]]]].
  pose proof Hacquire as [Hsave [Hbefore [Htype [Hlookup [Hcurrent Hgeneration]]]]].
  pose proof Hsave as [Hvalid Hrest].
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (q_post_wake_merge sg acquired_2 eid current tid old message priority
    Hvalid Hlookup Hcurrent Hentry).
  Intros released.
  pose proof (q_post_front_wake_critical sg acquired_2 eid current message priority released
    Hlookup Hgroup H) as Hcritical.
  destruct (q_post_wake_decompose sg acquired_2 eid current message priority released
    Hvalid Hlookup Hcurrent Hgroup H)
    as [head [tail [found [Hlist [Hfound [Hpriority [Hreleased [Hafter Hafterlookup]]]]]]]].
  assert (Hframe : q_post_mask_frame environment critical saved_local sg active_2 cpu_sr acquired_2 acquired_2 |--
    q_post_mask_frame environment critical saved_local sg active_2 cpu_sr acquired_2 released).
  { rewrite Hreleased; apply q_post_mask_frame_wake_update; exact Hfound. }
  sep_apply_l_atomic Hframe.
  Exists active_2 acquired_2 released.
  unfold q_post_front_restore_pre; rewrite q_post_masked_equiv.
  pose proof (q_post_acquire_original_type environment critical sg caller active_2 mask cpu_sr
    before acquired_2 eid observed current Hacquire) as Horiginal_type.
  assert (Heffect : q_post_front_effect sg eid message acquired_2 0 1 released).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE, true;
      split; [reflexivity|]; split; [reflexivity|exact Hcritical]. }
  entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_6 : OSQPostFront_which_implies_wit_6.
Proof.
  left; intros; apply q_post_front_restored_schedule_pre; assumption.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_7 : OSQPostFront_which_implies_wit_7.
Proof.
  left; intros; subst pevent.
  unfold q_post_group_context; Intros.
  destruct H as [Hacquire [Hprofile Heid]].
  pose proof Hacquire as [Hsave [_ [_ [Hlookup [Htype Hgeneration]]]]].
  pose proof Hsave as [Hvalid _].
  destruct (proj1 (proj2 Hprofile) eid Heid)
    as [[Htype_addr [Hptr_addr Hcount_addr]] [Hgroup_addr Htable_addr]].
  rewrite Hgroup_addr.
  sep_apply (q_post_group_cell_merge sg acquired_2 eid current_2 Hvalid Hlookup).
  destruct (q_post_queue_current sg acquired_2 eid current_2 Hvalid Hlookup Htype PreH2)
    as [q [Hqueue [Hempty Hconsistent]]].
  sep_apply (q_post_pointer_split sg acquired_2 eid current_2 q Hlookup Htype Hqueue).
  Intros.
  Exists active_2 acquired_2 current_2 q.
  unfold q_post_pointer_context; rewrite Hptr_addr; entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_8 : OSQPostFront_which_implies_wit_8.
Proof.
  left; intros; subst pq pevent.
  unfold q_post_pointer_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hzero [Hqueue [Hempty Hconsistent]]]]]].
  pose proof Hacquire as [Hsave [_ [_ [Hlookup [Htype Hgeneration]]]]].
  pose proof Hsave as [Hvalid _].
  destruct (proj1 (proj2 Hprofile) eid Heid)
    as [[Htype_addr [Hptr_addr Hcount_addr]] [Hgroup_addr Htable_addr]].
  rewrite Hptr_addr.
  sep_apply (q_post_pointer_merge sg acquired_2 eid current_2 q_2
    Hvalid Hlookup Htype Hqueue).
  sep_apply (q_post_queue_split sg acquired_2 eid current_2 q_2
    Hlookup Htype Hqueue Hempty).
  Intros free slots.
  pose proof (queue_entries_in_range sg nil q_2 Hconsistent) as Hcount.
  pose proof Hconsistent as [Hqid [_ [Hsize _]]].
  rewrite (q_post_front_qcb_cells_equiv sg q_2 Hprofile Hqid).
  Exists active_2 acquired_2 current_2 free slots q_2.
  unfold q_post_store_context, q_post_front_qcb_cells; entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_9 : OSQPostFront_which_implies_wit_9.
Proof.
  left; intros.
  unfold q_post_store_context; Intros.
  destruct H as [Hacquire [Hprofile [Hzero [Hbase Hfacts]]]]; subst pq.
  pose proof (proj1 Hacquire) as Hsave.
  pose proof Hfacts as [Hvalid [Hlookup [Htype [Hqueue [Hempty [Hconsistent Hrest]]]]]].
  pose proof (proj2 (q_post_front_qcb_cells_equiv sg q Hprofile (proj1 Hconsistent))) as Hcells.
  unfold q_post_front_qcb_cells in Hcells; sep_apply Hcells.
  sep_apply (q_post_queue_merge_original sg acquired_2 eid current q free slots Hfacts).
  pose proof (q_post_front_full_critical sg acquired_2 eid current q message
    Hlookup Hqueue Hzero ltac:(lia)) as Hcritical.
  assert (Heffect : q_post_front_effect sg eid message acquired_2 30 0 acquired_2).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_Q_FULL, false;
      split; [reflexivity|]; split; [reflexivity|exact Hcritical]. }
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbefore_type.
  Exists active_2 acquired_2.
  unfold q_post_front_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_10 : OSQPostFront_which_implies_wit_10.
Proof.
  left; intros.
  unfold q_post_store_context; Intros.
  pose proof H as [Hacquire [Hprofile [Hzero [Hbase Hfacts]]]].
  pose proof Hfacts as [Hvalid [Hlookup [Htype [Hqueue [Hempty [Hconsistent Hrest]]]]]].
  pose proof (q_post_front_nonfull_bounds sg q_2 Hconsistent PreH1)
    as [Hsize [Hout [Hcount Hnext]]].
  sep_apply (q_post_front_slot_split sg q_2 slots_2 Hconsistent PreH1).
  Intros.
  Exists active_2 acquired_2 current_2 free_2 slots_2 q_2.
  unfold q_post_store_context, q_post_front_slot_frame; entailer!.
Qed.

Lemma proof_of_OSQPostFront_which_implies_wit_11 : OSQPostFront_which_implies_wit_11.
Proof.
  left; intros.
  unfold q_post_store_context, q_post_front_slot_frame; Intros.
  destruct H as [Hacquire [Hprofile [Hzero [Hbase Hfacts]]]]; subst pq.
  pose proof (proj1 Hacquire) as Hsave.
  pose proof Hfacts as [Hvalid [Hlookup [Htype [Hqueue [Hempty
    [Hconsistent [Hbinding [Hpartition [Hslots Hmodel]]]]]]]]].
  pose proof (proj1 (q_post_front_qcb_enqueued_equiv sg q message Hprofile
    (proj1 Hconsistent) PreH2)) as Hcells.
  unfold q_post_front_qcb_cells in Hcells; sep_apply Hcells.
  sep_apply (q_post_front_enqueue_merge sg acquired_2 eid current q free slots message Hfacts PreH2).
  pose proof (q_post_front_enqueue_critical sg acquired_2 eid current q message slots
    Hlookup Hqueue Hzero Hslots PreH2) as Hcritical.
  pose proof (q_post_critical_preserves_validity sg QueuePostFront acquired_2 eid current message
    (Ucos2Verify.lib.error_codes.OS_ERR_NONE, false)
    (q_post_front_enqueue_state acquired_2 eid current q message slots)
    Hvalid Hlookup Htype Hcritical) as Hafter_valid.
  assert (Heffect : q_post_front_effect sg eid message acquired_2 0 0
    (q_post_front_enqueue_state acquired_2 eid current q message slots)).
  { exists Ucos2Verify.lib.error_codes.OS_ERR_NONE, false;
      split; [reflexivity|]; split; [reflexivity|exact Hcritical]. }
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbefore_type.
  sep_apply (q_post_mask_frame_event_update environment critical saved_local sg active_2 cpu_sr
    acquired_2 acquired_2 (q_post_front_enqueue_state acquired_2 eid current q message slots) eq_refl).
  Exists active_2 acquired_2 (q_post_front_enqueue_state acquired_2 eid current q message slots).
  unfold q_post_front_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

