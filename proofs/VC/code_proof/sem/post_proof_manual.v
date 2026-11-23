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
From Ucos2Verify.VC.code.sem Require Import post_goal.
From Ucos2Verify.VC.code.sem Require Import post_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_api_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSSemPost_entail_wit_1 : OSSemPost_entail_wit_1.
Proof.
  left; intros.
  prop_apply store_uchar_range.
  entailer!.
Qed.

Lemma proof_of_OSSemPost_return_wit_1 : OSSemPost_return_wit_1.
Proof.
  left; intros; rewrite <- PreH5.
  apply sem_post_api_nonschedule_return; exact PreH29.
Qed.

Lemma proof_of_OSSemPost_return_wit_2 : OSSemPost_return_wit_2.
Proof.
  left; intros; rewrite <- PreH5.
  apply sem_post_api_nonschedule_return; exact PreH29.
Qed.

Lemma proof_of_OSSemPost_return_wit_3 : OSSemPost_return_wit_3.
Proof.
  left; intros.
  destruct PreH1 as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  apply sem_post_api_sched_return with (restored := restored); assumption.
Qed.

Lemma proof_of_OSSemPost_return_wit_4 : OSSemPost_return_wit_4.
Proof.
  left; intros.
  assert (Hresult : sem_post_api_caller_result environment critical sg caller mask
    pe eid before 1 caller before).
  { exists caller, before, false; split; [|auto].
    unfold sem_post_api_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) PreH7),
      (proj2 (Z.eqb_neq _ _) PreH1); auto. }
  sep_apply_r_atomic (sem_post_api_closed_return environment critical saved_local sg
    caller caller mask pe eid before before 1 X Hresult PreH20).
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH11).
  unfold q_post_type_context.
  subst pe.
  destruct PreH9 as [[Htype_address _] _].
  rewrite Htype_address.
  sep_apply (sem_query_type_merge_full sg before eid PreH11).
  entailer!.
Qed.

Lemma proof_of_OSSemPost_return_wit_5 : OSSemPost_return_wit_5.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by lia; rewrite Hpe in *.
  apply sem_post_api_closed_return; [|exact PreH8].
  exists caller, before, false; split; [|auto].
  unfold sem_post_api_prefix_program; cbn; auto.
Qed.

Lemma proof_of_OSSemPost_return_wit_6 : OSSemPost_return_wit_6.
Proof.
  left; intros.
  assert (Hpe : pe = 0) by lia; rewrite Hpe in *.
  apply sem_post_api_closed_return; [|exact PreH8].
  exists caller, before, false; split; [|auto].
  unfold sem_post_api_prefix_program; cbn; auto.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_5_pure : OSSemPost_partial_solve_wit_5_pure.
Proof.
  left; intros.
  assert (Hgroup : sem_post_group acquired current <> 0).
  { intro Hzero; rewrite Hzero in PreH1; vm_compute in PreH1; contradiction. }
  entailer!.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_6_pure : OSSemPost_partial_solve_wit_6_pure.
Proof.
  left; intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in PreH28.
  entailer!; tauto.
Qed.

Lemma proof_of_OSSemPost_partial_solve_wit_11_pure : OSSemPost_partial_solve_wit_11_pure.
Proof.
  left; intros.
  prop_apply store_uchar_range; Intros.
  change (0 <= sem_post_group acquired current <= 255) in H.
  rewrite unsigned_last_nbits_eq in PreH1.
  - entailer!.
  - change (0 <= sem_post_group acquired current < 4294967296); lia.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_1 : OSSemPost_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH4 as Hinput.
  destruct Hinput as [Hzero|[Hnonnull [Haddr [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH3).
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  rewrite Haddr, (proj1 (proj1 PreH5)).
  unfold q_post_type_context; entailer!.
  rewrite <- Haddr; exact PreH4.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_2 : OSSemPost_which_implies_wit_2.
Proof.
  left; intros.
  rewrite PreH1, (proj1 (proj1 PreH4)).
  unfold q_post_type_context, sem_post_api_save_pre.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH6).
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before PreH6).
  entailer!.
  rewrite <- PreH1; exact PreH7.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_3 : OSSemPost_which_implies_wit_3.
Proof.
  left; intros.
  unfold sem_post_api_save_result; Intros active acquired current.
  pose proof H as [Hsave [Hobserved [Hobserved_type [Hcurrent [Htype Hgeneration]]]]].
  rewrite (q_post_masked_equiv environment critical saved_local sg active cpu_sr acquired acquired).
  sep_apply_l_atomic (sem_post_api_group_cell_split sg acquired eid current Hcurrent).
  Exists active acquired current.
  rewrite PreH1, (proj1 (proj2 PreH3)).
  unfold sem_post_api_group_context; entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_4 : OSSemPost_which_implies_wit_4.
Proof.
  left; intros.
  unfold sem_post_api_group_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid Hlayout]]].
  pose proof Hacquire as [Hsave [Hobserved [Hobserved_type [Hcurrent [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  rewrite PreH1, (proj1 (proj2 Hlayout)).
  sep_apply_l_atomic (sem_post_api_group_cell_merge sg acquired_2 eid current_2 Hvalid Hcurrent).
  sep_apply_l_atomic (sem_post_wake_split_full sg acquired_2 eid current_2
    Hvalid Hcurrent Htype PreH2 Hlayout).
  Intros tid old.
  Exists active_2 acquired_2 current_2 tid old.
  unfold sem_post_api_wake_context; entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_5 : OSSemPost_which_implies_wit_5.
Proof.
  left; intros.
  unfold sem_post_api_wake_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid [Hlayout [Hgroup Hentry]]]]].
  pose proof Hacquire as [Hsave [Hobserved [Hobserved_type [Hcurrent [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (sem_post_api_acquire_original_type environment critical sg caller active_2 mask
    cpu_sr before acquired_2 eid observed current Hacquire) as Horiginal_type.
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (sem_post_wake_merge_full sg acquired_2 eid current tid old priority
    Hvalid Hcurrent Htype Hentry).
  Intros released.
  pose proof (sem_post_wake_result_critical sg eid acquired_2 current released priority
    Hcurrent Hgroup H) as Hstep.
  destruct (sem_post_api_wake_state sg acquired_2 eid current OS_ERR_NONE released
    Hvalid Hcurrent Htype Hstep) as [selected [previous [Hused [Hreleased Hreleased_valid]]]].
  pose proof (sem_post_api_mask_frame_wake_update environment critical saved_local sg active_2
    cpu_sr acquired_2 acquired_2 eid current selected previous Hused) as Hframe.
  rewrite <- Hreleased in Hframe.
  sep_apply_l_atomic Hframe.
  Exists active_2 acquired_2 released.
  unfold sem_post_api_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active_2 cpu_sr acquired_2 released).
  entailer!.
  exists OS_ERR_NONE, true; repeat split; auto.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_6 : OSSemPost_which_implies_wit_6.
Proof.
  left; intros.
  exact (sem_post_api_restored_schedule_pre environment critical saved_local sg caller mask pe eid
    before 0 PreH1).
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_7 : OSSemPost_which_implies_wit_7.
Proof.
  left; intros.
  unfold sem_post_api_group_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid Hlayout]]].
  pose proof Hacquire as [Hsave [Hobserved [Hobserved_type [Hcurrent [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  rewrite PreH1, (proj1 (proj2 Hlayout)), (proj2 (proj2 (proj1 Hlayout))).
  sep_apply_l_atomic (sem_post_api_group_cell_merge sg acquired_2 eid current_2 Hvalid Hcurrent).
  sep_apply_l_atomic (sem_post_count_split_full sg acquired_2 eid current_2 Hcurrent Htype).
  Intros.
  Exists active_2 acquired_2 current_2.
  unfold sem_post_api_count_context; entailer!.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_8 : OSSemPost_which_implies_wit_8.
Proof.
  left; intros.
  unfold sem_post_api_count_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid [Hlayout [Hgroup Hrange]]]]].
  pose proof Hacquire as [Hsave [Hobserved [Hobserved_type [Hcurrent [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (sem_post_api_acquire_original_type environment critical sg caller active_2 mask
    cpu_sr before acquired_2 eid observed current Hacquire) as Horiginal_type.
  assert (Hroom : Z.ltb (encode_event_cnt_value current) 65535 = true)
    by (apply Z.ltb_lt; exact PreH4).
  pose proof (sem_post_count_checkpoint_critical sg acquired_2 eid current
    Hvalid Hcurrent Htype Hgroup) as Hstep.
  unfold sem_post_count_error in Hstep; rewrite Hroom in Hstep.
  pose proof (sem_post_critical_preserves_validity sg acquired_2 eid current (OS_ERR_NONE, false)
    (sem_post_count_checkpoint acquired_2 eid current) Hvalid Hcurrent Htype Hstep) as Hreleased_valid.
  pose proof (sem_post_count_merge_checkpoint sg acquired_2 eid current Hvalid Hcurrent Htype Hgroup) as Hmerge.
  unfold sem_post_stored_count in Hmerge; rewrite Hroom in Hmerge.
  rewrite PreH2, (proj2 (proj2 (proj1 Hlayout))).
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (sem_post_api_mask_frame_count_update environment critical saved_local sg active_2
    cpu_sr acquired_2 acquired_2 eid current).
  Exists active_2 acquired_2 (sem_post_count_checkpoint acquired_2 eid current).
  unfold sem_post_api_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active_2 cpu_sr acquired_2
    (sem_post_count_checkpoint acquired_2 eid current)).
  entailer!.
  exists OS_ERR_NONE, false; repeat split; auto.
Qed.

Lemma proof_of_OSSemPost_which_implies_wit_9 : OSSemPost_which_implies_wit_9.
Proof.
  left; intros.
  unfold sem_post_api_count_context; Intros.
  destruct H as [Hacquire [Hprofile [Hid [Hlayout [Hgroup Hrange]]]]].
  pose proof Hacquire as [Hsave [Hobserved [Hobserved_type [Hcurrent [Htype Hgeneration]]]]].
  pose proof (proj1 Hsave) as Hvalid.
  pose proof (sem_post_api_acquire_original_type environment critical sg caller active_2 mask
    cpu_sr before acquired_2 eid observed current Hacquire) as Horiginal_type.
  assert (Hfull : Z.ltb (encode_event_cnt_value current) 65535 = false)
    by (apply Z.ltb_ge; lia).
  pose proof (sem_post_count_checkpoint_critical sg acquired_2 eid current
    Hvalid Hcurrent Htype Hgroup) as Hstep.
  unfold sem_post_count_error in Hstep; rewrite Hfull in Hstep.
  pose proof (sem_post_critical_preserves_validity sg acquired_2 eid current (OS_ERR_SEM_OVF, false)
    (sem_post_count_checkpoint acquired_2 eid current) Hvalid Hcurrent Htype Hstep) as Hreleased_valid.
  pose proof (sem_post_count_merge_checkpoint sg acquired_2 eid current Hvalid Hcurrent Htype Hgroup) as Hmerge.
  unfold sem_post_stored_count in Hmerge; rewrite Hfull in Hmerge.
  rewrite PreH2, (proj2 (proj2 (proj1 Hlayout))).
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (sem_post_api_mask_frame_count_update environment critical saved_local sg active_2
    cpu_sr acquired_2 acquired_2 eid current).
  Exists active_2 acquired_2 (sem_post_count_checkpoint acquired_2 eid current).
  unfold sem_post_api_restore_pre.
  rewrite (q_post_masked_equiv environment critical saved_local sg active_2 cpu_sr acquired_2
    (sem_post_count_checkpoint acquired_2 eid current)).
  entailer!.
  exists OS_ERR_SEM_OVF, false; repeat split; auto.
Qed.

