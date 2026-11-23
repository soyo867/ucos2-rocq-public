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
From Ucos2Verify.VC.code.core Require Import task_stat_goal.
From Ucos2Verify.VC.code.core Require Import task_stat_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.task_stat_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_TaskStat_entail_wit_3 : OS_TaskStat_entail_wit_3.
Proof.
  unfold OS_TaskStat_entail_wit_3; left; intros.
  pose proof PreH1 as [_ [Henabled _]].
  unfold task_stat_closed_statistics_frame at 1; Intros.
  match goal with H : ucos2_verify_inv.UCOS2_state_inv sg rs |- _ => pose proof H as Hstate end.
  assert (Hstatistics : valid_statistics_configuration sg (StatsState rs)).
  { unfold ucos2_verify_inv.UCOS2_state_inv, ucos2_verify_inv.UCOS2_state_inv_with_ready in Hstate; tauto. }
  assert (Hquot : Z.quot (task_stat_maximum rs) 100 = task_stat_maximum rs / 100).
  { apply Z.quot_div_nonneg; [|lia].
    destruct Hstatistics as [Hstats _]; unfold valid_statistics_state, task_stat_maximum in *; lia. }
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS
      (statistics_store_state StatisticsCalibrationField (task_stat_maximum rs / 100) (StatsState rs)) rs)).
  { apply statistics_replace_preserves_validity; [exact Hstate|].
    apply statistics_enabled_update_preserves_configuration; [exact Henabled| |exact Hstatistics].
    intros; apply statistics_store_preserves_validity; assumption. }
  assert (Hloaded : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatScaleStore (task_stat_maximum rs)) rc rm) rs X).
  { eapply task_stat_context_step; [exact PreH5|apply task_stat_step_scale_load]. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at TaskStatZeroTest rc rm)
    (ucos2_verify_state_def.replace_StatsS
      (statistics_store_state StatisticsCalibrationField (task_stat_maximum rs / 100) (StatsState rs)) rs) X).
  { eapply task_stat_context_step; [exact Hloaded|]. eapply task_stat_step_store; reflexivity. }
  Exists rc rm (ucos2_verify_state_def.replace_StatsS
    (statistics_store_state StatisticsCalibrationField (task_stat_maximum rs / 100) (StatsState rs)) rs).
  entailer!.
  unfold task_stat_closed_statistics_frame.
  rewrite task_stat_outside_resources_replace_statistics.
  pose proof (task_stat_missing_statistics_replace_eq sg rs
    (statistics_store_state StatisticsCalibrationField (task_stat_maximum rs / 100) (StatsState rs))) as Hrest.
  unfold ucos2_spatial.UCOS2_raw_rep_missing_statistics in Hrest.
  rewrite <- Hrest.
  cbn [task_stat_counter task_stat_maximum task_stat_run task_stat_usage task_stat_ready
    ucos2_verify_state_def.replace_StatsS statistics_store_state].
  rewrite Hquot.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_5 : OS_TaskStat_entail_wit_5.
Proof.
  unfold OS_TaskStat_entail_wit_5; left; intros.
  pose proof PreH1 as [_ [Henabled _]].
  pose proof PreH2 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  unfold task_stat_closed_statistics_frame at 1; Intros.
  match goal with H : ucos2_verify_inv.UCOS2_state_inv sg zs |- _ => pose proof H as Hstate end.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField 0 (StatsState zs)) zs)).
  { apply statistics_replace_preserves_validity; [exact Hstate|].
    apply statistics_enabled_update_preserves_configuration; [exact Henabled| |].
    - intros; apply statistics_store_preserves_validity; assumption.
    - unfold ucos2_verify_inv.UCOS2_state_inv, ucos2_verify_inv.UCOS2_state_inv_with_ready in Hstate; tauto. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at TaskStatSelfSuspend zc zm)
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField 0 (StatsState zs)) zs) X).
  { eapply task_stat_context_step; [exact PreH5|]. eapply task_stat_step_store; reflexivity. }
  Exists (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField 0 (StatsState zs)) zs).
  unfold task_stat_closed_checkpoint; entailer!.
  pose proof (task_stat_closed_merge_statistics environment critical saved_local sg zc zm zs
    (statistics_store_state StatisticsUsageField 0 (StatsState zs)) Hvalid) as Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold statistics_rep, task_stat_closed_statistics_frame.
  rewrite Henabled, Hctr, Hmax, Hrun, Husage, Hready.
  cbn [statistics_store_state kernel_resources.kernel_u8].
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_6 : OS_TaskStat_entail_wit_6.
Proof.
  pre_process.
  assert (Hconfiguration : task_stat_configuration sg) by assumption.
  pose proof Hconfiguration as Hcfg.
  destruct Hcfg as [Hvalid [Hstatistics [[Hchecks [Hlowest Hself]] Hprofile]]].
  pose proof (task_stat_suspend_self_no_argument_error sg Hconfiguration) as Hargument.
  pose proof (task_stat_suspend_post_context environment critical saved_local sg frame
    zc zm zero_written retval X Hargument) as Hpost.
  rewrite Hself in Hpost.
  sep_apply_l_atomic Hpost.
  Intros suspend_returned suspend_current.
  Exists suspend_returned suspend_current.
  rewrite (task_stat_closed_split_statistics environment critical saved_local sg
    suspend_returned zm suspend_current).
  unfold statistics_rep; rewrite Hstatistics.
  match goal with H : task_stat_statistics_addresses _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses end.
  destruct Haddresses as [Hctr [Hmaximum [Hrun [Husage Hready]]]].
  unfold task_stat_counter, task_stat_maximum, task_stat_run,
    task_stat_usage, task_stat_ready.
  rewrite Hctr, Hmaximum, Hrun, Husage, Hready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_8 : OS_TaskStat_entail_wit_8.
Proof.
  Unfold. left. intros.
  rewrite (task_stat_save_post_context environment critical saved_local sg frame
    TaskStatInitialize zc zm retval zs X PreH1).
  Intros returned acquired.
  unfold task_stat_masked_checkpoint.
  Intros.
  rewrite task_stat_masked_split_statistics.
  pose proof (proj1 (proj2 PreH2)) as Hstatistics.
  pose proof PreH3 as [Hcounter [Hmaximum [Hrun [Husage Hready]]]].
  unfold statistics_rep.
  rewrite Hstatistics, Hcounter, Hmaximum, Hrun, Husage, Hready.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  Exists returned acquired.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_9 : OS_TaskStat_entail_wit_9.
Proof.
  unfold OS_TaskStat_entail_wit_9; left; intros.
  pose proof PreH1 as [_ [Henabled _]].
  pose proof PreH2 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  unfold task_stat_masked_statistics_frame at 1; Intros.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS
      (task_stat_protected_statistics TaskStatInitialize (StatsState init_acquired)) init_acquired)).
  { apply task_stat_protected_valid; assumption. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatRelease TaskStatInitialize cpu_sr init_acquired (task_stat_sample 0 0))
      init_caller zm)
    (ucos2_verify_state_def.replace_StatsS
      (task_stat_protected_statistics TaskStatInitialize (StatsState init_acquired)) init_acquired) X).
  { eapply task_stat_context_step; [exact PreH5|apply task_stat_step_protected]. }
  Exists (ucos2_verify_state_def.replace_StatsS
    (task_stat_protected_statistics TaskStatInitialize (StatsState init_acquired)) init_acquired).
  entailer!.
  pose proof (task_stat_masked_merge_statistics environment critical saved_local sg
    init_caller cpu_sr init_acquired init_acquired
    (task_stat_protected_statistics TaskStatInitialize (StatsState init_acquired)) Hvalid) as Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold statistics_rep, task_stat_masked_statistics_frame.
  rewrite Henabled, Hctr, Hmax, Hrun, Husage, Hready.
  cbn [task_stat_protected_statistics task_stat_initial_counter statistics_set_counter].
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_10 : OS_TaskStat_entail_wit_10.
Proof.
  Unfold. left. intros.
  sep_apply (task_stat_restore_post_context environment critical saved_local sg frame
    TaskStatInitialize (task_stat_sample 0 0) init_caller zm cpu_sr
    init_acquired init_released X PreH5).
  Intros returned current.
  Exists returned (armv7a_irq_fiq_mask cpu_sr) current.
  cbn [task_stat_after_release].
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_12 : OS_TaskStat_entail_wit_12.
Proof.
  Unfold. left. intros.
  rewrite (task_stat_save_post_context environment critical saved_local sg frame
    TaskStatReset one_returned lm retval one_current X PreH1).
  Intros returned acquired.
  unfold task_stat_masked_checkpoint.
  Intros.
  rewrite task_stat_masked_split_statistics.
  pose proof (proj1 (proj2 PreH3)) as Hstatistics.
  pose proof PreH4 as [Hcounter [Hmaximum [Hrun [Husage Hready]]]].
  unfold statistics_rep.
  rewrite Hstatistics, Hcounter, Hmaximum, Hrun, Husage, Hready.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  Exists returned acquired.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_13 : OS_TaskStat_entail_wit_13.
Proof.
  unfold OS_TaskStat_entail_wit_13; left; intros.
  pose proof PreH1 as [_ [Henabled _]].
  pose proof PreH2 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  unfold task_stat_masked_statistics_frame at 1; Intros.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS
      (task_stat_protected_statistics TaskStatReset (StatsState reset_acquired)) reset_acquired)).
  { apply task_stat_protected_valid; assumption. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatRelease TaskStatReset cpu_sr reset_acquired (task_stat_sample 0 0))
      reset_caller lm)
    (ucos2_verify_state_def.replace_StatsS
      (task_stat_protected_statistics TaskStatReset (StatsState reset_acquired)) reset_acquired) X).
  { eapply task_stat_context_step; [exact PreH5|apply task_stat_step_protected]. }
  Exists (ucos2_verify_state_def.replace_StatsS
    (task_stat_protected_statistics TaskStatReset (StatsState reset_acquired)) reset_acquired).
  entailer!.
  pose proof (task_stat_masked_merge_statistics environment critical saved_local sg
    reset_caller cpu_sr reset_acquired reset_acquired
    (task_stat_protected_statistics TaskStatReset (StatsState reset_acquired)) Hvalid) as Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold statistics_rep, task_stat_masked_statistics_frame.
  rewrite Henabled, Hctr, Hmax, Hrun, Husage, Hready.
  cbn [task_stat_protected_statistics statistics_reset_counter statistics_set_counter kernel_resources.kernel_u32].
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_14 : OS_TaskStat_entail_wit_14.
Proof.
  Unfold. left. intros.
  sep_apply (task_stat_restore_post_context environment critical saved_local sg frame
    TaskStatReset (task_stat_sample 0 0) reset_caller lm cpu_sr
    reset_acquired reset_released X PreH5).
  Intros returned current.
  Exists returned (armv7a_irq_fiq_mask cpu_sr) current.
  cbn [task_stat_after_release].
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_15 : OS_TaskStat_entail_wit_15.
Proof.
  Unfold. left. intros.
  rewrite (task_stat_save_post_context environment critical saved_local sg frame
    TaskStatCapture window_returned window_mask retval window_current X PreH1).
  Intros returned acquired.
  unfold task_stat_masked_checkpoint.
  Intros.
  rewrite task_stat_masked_split_statistics.
  pose proof (proj1 (proj2 PreH3)) as Hstatistics.
  pose proof PreH4 as [Hcounter [Hmaximum [Hrun [Husage Hready]]]].
  unfold statistics_rep.
  rewrite Hstatistics, Hcounter, Hmaximum, Hrun, Husage, Hready.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  Exists returned acquired.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_16 : OS_TaskStat_entail_wit_16.
Proof.
  unfold OS_TaskStat_entail_wit_16; left; intros.
  pose proof PreH1 as [_ [Henabled _]].
  pose proof PreH2 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  unfold task_stat_masked_statistics_frame at 1; Intros.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS
      (task_stat_protected_statistics TaskStatCapture (StatsState capture_acquired)) capture_acquired)).
  { apply task_stat_protected_valid; assumption. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatRelease TaskStatCapture cpu_sr capture_acquired (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)))
      capture_caller window_mask)
    (ucos2_verify_state_def.replace_StatsS
      (task_stat_protected_statistics TaskStatCapture (StatsState capture_acquired)) capture_acquired) X).
  { eapply task_stat_context_step; [exact PreH5|apply task_stat_step_protected]. }
  assert (Hsample : valid_statistics_sample
    (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired))).
  { match goal with H : ucos2_verify_inv.UCOS2_state_inv sg capture_acquired |- _ =>
      pose proof H as Hstatistics end.
    unfold ucos2_verify_inv.UCOS2_state_inv, ucos2_verify_inv.UCOS2_state_inv_with_ready in Hstatistics.
    assert (Hcfg : valid_statistics_configuration sg (StatsState capture_acquired)) by tauto.
    destruct Hcfg as [Hstats _].
    exact (proj1 (statistics_capture_preserves_validity (StatsState capture_acquired) Hstats)). }
  Exists (ucos2_verify_state_def.replace_StatsS
    (task_stat_protected_statistics TaskStatCapture (StatsState capture_acquired)) capture_acquired).
  entailer!.
  pose proof (task_stat_masked_merge_statistics environment critical saved_local sg
    capture_caller cpu_sr capture_acquired capture_acquired
    (task_stat_protected_statistics TaskStatCapture (StatsState capture_acquired)) Hvalid) as Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold statistics_rep, task_stat_masked_statistics_frame.
  rewrite Henabled, Hctr, Hmax, Hrun, Husage, Hready.
  cbn [task_stat_protected_statistics statistics_capture].
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_17 : OS_TaskStat_entail_wit_17.
Proof.
  Unfold. left. intros.
  sep_apply (task_stat_restore_post_context environment critical saved_local sg frame
    TaskStatCapture (task_stat_sample (task_stat_counter capture_acquired)
      (task_stat_maximum capture_acquired)) capture_caller window_mask cpu_sr
    capture_acquired capture_released X PreH5).
  Intros returned current.
  sep_apply store_uint_undef_store_uint.
  unfold task_stat_closed_checkpoint.
  Intros.
  rewrite task_stat_closed_split_statistics.
  pose proof (proj1 (proj2 PreH1)) as Hstatistics.
  pose proof PreH2 as [Hcounter [Hmaximum [Hrun [Husage Hready]]]].
  unfold statistics_rep.
  rewrite Hstatistics, Hcounter, Hmaximum, Hrun, Husage, Hready.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  Exists returned (armv7a_irq_fiq_mask cpu_sr) current.
  cbn [task_stat_after_release] in *.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_18 : OS_TaskStat_entail_wit_18.
Proof.
  unfold OS_TaskStat_entail_wit_18; left; intros.
  pose proof PreH3 as [_ [Henabled _]].
  pose proof PreH4 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  assert (Hsample : valid_statistics_sample (task_stat_sample idle_run idle_max)).
  { rewrite PreH7, PreH8; exact PreH9. }
  unfold valid_statistics_sample, task_stat_sample in Hsample; cbn in Hsample.
  destruct Hsample as [[Hr0 Hrmax] [Hd0 Hdmax]].
  assert (Hquot : Z.quot idle_run idle_max = idle_run / idle_max)
    by (apply Z.quot_div_nonneg; lia).
  rewrite Hquot in PreH1.
  assert (Hzero : (idle_max =? 0) = false) by (apply Z.eqb_neq; exact PreH2).
  assert (Hratio : (idle_run / idle_max <=? 100) = false)
    by (apply Z.leb_gt; lia).
  assert (Husage_eq : task_stat_sample_usage (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)) = 0).
  { unfold task_stat_sample_usage; cbv beta iota zeta delta [task_stat_sample sampleRun sampleDivisor].
    rewrite <- PreH7, <- PreH8, Hzero, Hratio; reflexivity. }
  assert (Hnext : task_stat_after_usage (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)) = (TaskStatRecalibrate (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)))).
  { unfold task_stat_after_usage, task_stat_needs_recalibration; cbv beta iota zeta delta [task_stat_sample sampleRun sampleDivisor].
    rewrite <- PreH7, <- PreH8, Hzero, Hratio; reflexivity. }
  unfold task_stat_closed_statistics_frame at 1; Intros.
  match goal with H : ucos2_verify_inv.UCOS2_state_inv sg sample_state |- _ => pose proof H as Hstate end.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField (0) (StatsState sample_state)) sample_state)).
  { apply statistics_replace_preserves_validity; [exact Hstate|].
    apply statistics_enabled_update_preserves_configuration; [exact Henabled| |].
    - intros; apply statistics_store_preserves_validity; assumption.
    - unfold ucos2_verify_inv.UCOS2_state_inv, ucos2_verify_inv.UCOS2_state_inv_with_ready in Hstate; tauto. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatRecalibrate (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired))) sample_caller sample_mask)
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField (0)
      (StatsState sample_state)) sample_state) X).
  { eapply task_stat_context_step; [exact PreH10|].
    eapply task_stat_step_store.
    cbn [task_stat_store_instruction]; rewrite Husage_eq, Hnext; reflexivity. }
  Exists (ucos2_verify_state_def.replace_StatsS
    (statistics_store_state StatisticsUsageField 0 (StatsState sample_state)) sample_state).
  rewrite Hquot; entailer!.
  unfold task_stat_closed_statistics_frame.
  rewrite task_stat_outside_resources_replace_statistics.
  pose proof (task_stat_missing_statistics_replace_eq sg sample_state
    (statistics_store_state StatisticsUsageField 0 (StatsState sample_state))) as Hrest.
  unfold ucos2_spatial.UCOS2_raw_rep_missing_statistics in Hrest; rewrite <- Hrest.
  cbn [task_stat_counter task_stat_maximum task_stat_run task_stat_usage task_stat_ready
    ucos2_verify_state_def.replace_StatsS statistics_store_state kernel_resources.kernel_u8].
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_19_1 : OS_TaskStat_entail_wit_19_1.
Proof.
  unfold OS_TaskStat_entail_wit_19_1; left; intros.
  pose proof PreH2 as [_ [Henabled _]].
  pose proof PreH3 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  assert (Husage_eq : task_stat_sample_usage (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)) = 0).
  { unfold task_stat_sample_usage; cbv beta iota zeta delta [task_stat_sample sampleRun sampleDivisor].
    rewrite <- PreH7, PreH1; reflexivity. }
  assert (Hnext : task_stat_after_usage (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)) = TaskStatHook).
  { unfold task_stat_after_usage, task_stat_needs_recalibration; cbv beta iota zeta delta [task_stat_sample sampleRun sampleDivisor].
    rewrite <- PreH7, PreH1; reflexivity. }
  unfold task_stat_closed_statistics_frame at 1; Intros.
  match goal with H : ucos2_verify_inv.UCOS2_state_inv sg sample_state |- _ => pose proof H as Hstate end.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField (0) (StatsState sample_state)) sample_state)).
  { apply statistics_replace_preserves_validity; [exact Hstate|].
    apply statistics_enabled_update_preserves_configuration; [exact Henabled| |].
    - intros; apply statistics_store_preserves_validity; assumption.
    - unfold ucos2_verify_inv.UCOS2_state_inv, ucos2_verify_inv.UCOS2_state_inv_with_ready in Hstate; tauto. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at TaskStatHook sample_caller sample_mask)
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField 0
      (StatsState sample_state)) sample_state) X).
  { eapply task_stat_context_step; [exact PreH9|].
    eapply task_stat_step_store.
    cbn [task_stat_store_instruction]; rewrite Husage_eq, Hnext; reflexivity. }
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_run")) idle_run).
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_max")) idle_max).
  Exists sample_caller sample_mask (ucos2_verify_state_def.replace_StatsS
    (statistics_store_state StatisticsUsageField 0 (StatsState sample_state)) sample_state).
  unfold task_stat_closed_checkpoint; entailer!.
  pose proof (task_stat_closed_merge_statistics environment critical saved_local sg sample_caller sample_mask sample_state
    (statistics_store_state StatisticsUsageField (0) (StatsState sample_state)) Hvalid) as Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold statistics_rep, task_stat_closed_statistics_frame.
  rewrite Henabled, Hctr, Hmax, Hrun, Husage, Hready.
  cbn [statistics_store_state kernel_resources.kernel_u8].
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_19_2 : OS_TaskStat_entail_wit_19_2.
Proof.
  unfold OS_TaskStat_entail_wit_19_2; left; intros.
  pose proof PreH3 as [_ [Henabled _]].
  pose proof PreH4 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  assert (Hsample : valid_statistics_sample (task_stat_sample idle_run idle_max)).
  { rewrite PreH7, PreH8; exact PreH9. }
  unfold valid_statistics_sample, task_stat_sample in Hsample; cbn in Hsample.
  destruct Hsample as [[Hr0 Hrmax] [Hd0 Hdmax]].
  assert (Hquot : Z.quot idle_run idle_max = idle_run / idle_max)
    by (apply Z.quot_div_nonneg; lia).
  rewrite Hquot in PreH1.
  assert (Hzero : (idle_max =? 0) = false) by (apply Z.eqb_neq; exact PreH2).
  assert (Hratio : (idle_run / idle_max <=? 100) = true)
    by (apply Z.leb_le; lia).
  assert (Husage_eq : task_stat_sample_usage (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)) = 100 - idle_run / idle_max).
  { unfold task_stat_sample_usage; cbv beta iota zeta delta [task_stat_sample sampleRun sampleDivisor].
    rewrite <- PreH7, <- PreH8, Hzero, Hratio; reflexivity. }
  assert (Hnext : task_stat_after_usage (task_stat_sample (task_stat_counter capture_acquired) (task_stat_maximum capture_acquired)) = TaskStatHook).
  { unfold task_stat_after_usage, task_stat_needs_recalibration; cbv beta iota zeta delta [task_stat_sample sampleRun sampleDivisor].
    rewrite <- PreH7, <- PreH8, Hzero, Hratio; reflexivity. }
  unfold task_stat_closed_statistics_frame at 1; Intros.
  match goal with H : ucos2_verify_inv.UCOS2_state_inv sg sample_state |- _ => pose proof H as Hstate end.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField (100 - idle_run / idle_max) (StatsState sample_state)) sample_state)).
  { apply statistics_replace_preserves_validity; [exact Hstate|].
    apply statistics_enabled_update_preserves_configuration; [exact Henabled| |].
    - intros; apply statistics_store_preserves_validity; assumption.
    - unfold ucos2_verify_inv.UCOS2_state_inv, ucos2_verify_inv.UCOS2_state_inv_with_ready in Hstate; tauto. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at TaskStatHook sample_caller sample_mask)
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsUsageField (100 - idle_run / idle_max)
      (StatsState sample_state)) sample_state) X).
  { eapply task_stat_context_step; [exact PreH10|].
    eapply task_stat_step_store.
    cbn [task_stat_store_instruction]; rewrite Husage_eq, Hnext; reflexivity. }
  assert (Hvalue : 0 <= 100 - idle_run / idle_max < 256).
  { assert (Hnonnegative : 0 <= idle_run / idle_max) by (apply Z.div_pos; lia); lia. }
  rewrite Hquot.
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_run")) idle_run).
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_max")) idle_max).
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_pct")) (idle_run / idle_max)).
  Exists sample_caller sample_mask (ucos2_verify_state_def.replace_StatsS
    (statistics_store_state StatisticsUsageField (100 - idle_run / idle_max) (StatsState sample_state)) sample_state).
  unfold task_stat_closed_checkpoint; entailer!.
  pose proof (task_stat_closed_merge_statistics environment critical saved_local sg sample_caller sample_mask sample_state
    (statistics_store_state StatisticsUsageField (100 - idle_run / idle_max) (StatsState sample_state)) Hvalid) as Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold statistics_rep, task_stat_closed_statistics_frame.
  rewrite Henabled, Hctr, Hmax, Hrun, Husage, Hready.
  cbn [statistics_store_state].
  rewrite kernel_resources.kernel_u8_identity by exact Hvalue.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_entail_wit_19_3 : OS_TaskStat_entail_wit_19_3.
Proof.
  unfold OS_TaskStat_entail_wit_19_3; left; intros.
  pose proof PreH1 as [_ [Henabled _]].
  pose proof PreH2 as [Hctr [Hmax [Hrun [Husage Hready]]]].
  assert (Hsample : valid_statistics_sample (task_stat_sample idle_run idle_max)).
  { rewrite PreH5, PreH6; exact PreH7. }
  unfold valid_statistics_sample, task_stat_sample in Hsample; cbn in Hsample.
  destruct Hsample as [[Hr0 Hrmax] [Hd0 Hdmax]].
  assert (Hquot : Z.quot idle_run 100 = idle_run / 100) by (apply Z.quot_div_nonneg; lia).
  unfold task_stat_closed_statistics_frame at 1; Intros.
  match goal with H : ucos2_verify_inv.UCOS2_state_inv sg usage_written |- _ => pose proof H as Hstate end.
  assert (Hvalid : ucos2_verify_inv.UCOS2_state_inv sg
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsCalibrationField (idle_run / 100) (StatsState usage_written)) usage_written)).
  { apply statistics_replace_preserves_validity; [exact Hstate|].
    apply statistics_enabled_update_preserves_configuration; [exact Henabled| |].
    - intros; apply statistics_store_preserves_validity; assumption.
    - unfold ucos2_verify_inv.UCOS2_state_inv, ucos2_verify_inv.UCOS2_state_inv_with_ready in Hstate; tauto. }
  assert (Hcontext : task_stat_context environment critical saved_local sg frame
    (task_stat_at TaskStatHook sample_caller sample_mask)
    (ucos2_verify_state_def.replace_StatsS (statistics_store_state StatisticsCalibrationField (idle_run / 100)
      (StatsState usage_written)) usage_written) X).
  { eapply task_stat_context_step; [exact PreH10|].
    eapply task_stat_step_store.
    cbn [task_stat_store_instruction task_stat_sample]; rewrite <- PreH5; reflexivity. }
  rewrite Hquot.
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_run")) idle_run).
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_max")) idle_max).
  sep_apply (UCOS2_C_Rules.store_uint_undef_store_uint (&("idle_pct")) idle_pct).
  Exists sample_caller sample_mask (ucos2_verify_state_def.replace_StatsS
    (statistics_store_state StatisticsCalibrationField (idle_run / 100) (StatsState usage_written)) usage_written).
  unfold task_stat_closed_checkpoint; entailer!.
  pose proof (task_stat_closed_merge_statistics environment critical saved_local sg sample_caller sample_mask usage_written
    (statistics_store_state StatisticsCalibrationField (idle_run / 100) (StatsState usage_written)) Hvalid) as Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold statistics_rep, task_stat_closed_statistics_frame.
  rewrite Henabled, Hctr, Hmax, Hrun, Husage, Hready.
  cbn [statistics_store_state kernel_resources.kernel_u8].
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_partial_solve_wit_2_pure : OS_TaskStat_partial_solve_wit_2_pure.
Proof.
  left; intros.
  unfold task_stat_ready in PreH1 |- *.
  destruct (statReady (StatsState rs)).
  - change (1 = 0) in PreH1; discriminate.
  - entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_partial_solve_wit_7_pure : OS_TaskStat_partial_solve_wit_7_pure.
Proof.
  left; intros.
  unfold task_stat_ready in PreH1 |- *.
  destruct (statReady (StatsState rs)).
  - entailer!.
  - change (0 <> 0) in PreH1; contradiction.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_1 : OS_TaskStat_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH1 as Hconfiguration.
  destruct Hconfiguration as [_ [Henabled _]].
  pose proof PreH2 as Haddresses.
  unfold task_stat_statistics_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmaximum [Hrun [Husage Hready_address]]]].
  unfold task_stat_closed_checkpoint.
  rewrite (task_stat_closed_split_statistics environment critical saved_local sg original initial_mask before).
  unfold statistics_rep; rewrite Henabled.
  rewrite Hcounter, Hmaximum, Hrun, Husage, Hready_address.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_2 : OS_TaskStat_which_implies_wit_2.
Proof.
  left; intros.
  assert (Hready : statReady (StatsState rs) = false).
  { unfold task_stat_ready in PreH1.
    destruct (statReady (StatsState rs)); congruence. }
  pose proof (task_stat_step_ready environment critical saved_local sg frame rc rm rs) as Hstep.
  rewrite Hready in Hstep.
  pose proof (task_stat_context_step environment critical saved_local sg frame _ _ _ _ X PreH6 Hstep) as Hnext.
  pose proof PreH2 as Hconfiguration.
  destruct Hconfiguration as [_ [Henabled _]].
  pose proof PreH3 as Haddresses.
  unfold task_stat_statistics_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmaximum [Hrun [Husage Hready_address]]]].
  unfold task_stat_closed_checkpoint.
  rewrite (task_stat_closed_split_statistics environment critical saved_local sg rc rm rs).
  unfold statistics_rep; rewrite Henabled.
  rewrite Hcounter, Hmaximum, Hrun, Husage, Hready_address.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_3 : OS_TaskStat_which_implies_wit_3.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint; Intros.
  match goal with Hcontext : task_stat_context _ _ _ _ _ _ _ _ |- _ =>
    pose proof (task_stat_context_delay_safe environment critical saved_local sg frame
      TaskStatReadyDelay rc rm 20 TaskStatReady rs X eq_refl Hcontext) as Hsafe;
    sep_apply_l_atomic (task_stat_delay_call_pre environment critical saved_local sg frame
      TaskStatReadyDelay rc rm 20 TaskStatReady rs X eq_refl Hcontext)
  end.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_4 : OS_TaskStat_which_implies_wit_4.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint.
  apply task_stat_delay_post_context.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_5 : OS_TaskStat_which_implies_wit_5.
Proof.
  left; intros.
  pose proof PreH1 as Hconfiguration.
  destruct Hconfiguration as [_ [Henabled _]].
  pose proof PreH2 as Haddresses.
  unfold task_stat_statistics_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmaximum [Hrun [Husage Hready_address]]]].
  unfold task_stat_closed_checkpoint.
  rewrite (task_stat_closed_split_statistics environment critical saved_local sg ready_returned rm ready_current).
  unfold statistics_rep; rewrite Henabled.
  rewrite Hcounter, Hmaximum, Hrun, Husage, Hready_address.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_6 : OS_TaskStat_which_implies_wit_6.
Proof.
  left; intros.
  assert (Hready : statReady (StatsState rs) = true).
  { unfold task_stat_ready in PreH1.
    destruct (statReady (StatsState rs)); congruence. }
  pose proof (task_stat_step_ready environment critical saved_local sg frame rc rm rs) as Hstep.
  rewrite Hready in Hstep.
  pose proof (task_stat_context_step environment critical saved_local sg frame _ _ _ _ X PreH6 Hstep) as Hnext.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_7 : OS_TaskStat_which_implies_wit_7.
Proof.
  left; intros.
  pose proof (task_stat_step_zero_test environment critical saved_local sg frame zc zm zs) as Hstep.
  unfold task_stat_maximum in PreH1.
  rewrite PreH1 in Hstep; cbn in Hstep.
  pose proof (task_stat_context_step environment critical saved_local sg frame _ _ _ _ X PreH6 Hstep) as Hnext.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_8 : OS_TaskStat_which_implies_wit_8.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint; Intros.
  assert (Hconfiguration : task_stat_configuration sg) by assumption.
  pose proof Hconfiguration as Hcfg.
  destruct Hcfg as [Hvalid [Hstatistics [[Hchecks [Hlowest Hself]] Hprofile]]].
  match goal with Hcontext : task_stat_context _ _ _ _ _ _ _ _ |- _ =>
    pose proof (task_stat_context_suspend_safe environment critical saved_local sg frame
      zc zm zero_written X Hcontext) as Hsafe;
    pose proof (task_stat_suspend_call_pre environment critical saved_local sg frame
      zc zm zero_written X Hconfiguration Hcontext) as Hpre
  end.
  apply task_stat_suspend_safe_observation in Hsafe.
  rewrite Hself in Hsafe, Hpre.
  sep_apply_l_atomic Hpre.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_9 : OS_TaskStat_which_implies_wit_9.
Proof.
  left; intros.
  assert (Hzero : Z.eqb (idleCtrMax (StatsState zs)) 0 = false).
  { apply Z.eqb_neq; exact PreH1. }
  pose proof (task_stat_step_zero_test environment critical saved_local sg frame zc zm zs) as Hstep.
  rewrite Hzero in Hstep.
  pose proof (task_stat_context_step environment critical saved_local sg frame _ _ _ _ X PreH6 Hstep) as Hnext.
  pose proof PreH2 as Hconfiguration.
  destruct Hconfiguration as [_ [Henabled _]].
  pose proof PreH3 as Haddresses.
  unfold task_stat_statistics_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmaximum [Hrun [Husage Hready_address]]]].
  unfold task_stat_closed_checkpoint.
  rewrite (task_stat_closed_split_statistics environment critical saved_local sg zc zm zs).
  unfold statistics_rep; rewrite Henabled.
  rewrite Hcounter, Hmaximum, Hrun, Husage, Hready_address.
  unfold task_stat_counter, task_stat_maximum, task_stat_run, task_stat_usage, task_stat_ready.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_10 : OS_TaskStat_which_implies_wit_10.
Proof.
  Unfold. left. intros.
  unfold task_stat_closed_checkpoint.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_11 : OS_TaskStat_which_implies_wit_11.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint; Intros.
  match goal with Hcontext : task_stat_context _ _ _ _ _ _ _ _ |- _ =>
    pose proof (task_stat_context_delay_safe environment critical saved_local sg frame
      TaskStatOneTick lc lm 1 (TaskStatAcquire TaskStatReset) ls X eq_refl Hcontext) as Hsafe;
    sep_apply_l_atomic (task_stat_delay_call_pre environment critical saved_local sg frame
      TaskStatOneTick lc lm 1 (TaskStatAcquire TaskStatReset) ls X eq_refl Hcontext)
  end.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_12 : OS_TaskStat_which_implies_wit_12.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint.
  apply task_stat_delay_post_context.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_13 : OS_TaskStat_which_implies_wit_13.
Proof.
  Unfold. left. intros.
  unfold task_stat_closed_checkpoint.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_14 : OS_TaskStat_which_implies_wit_14.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint; Intros.
  match goal with Hcontext : task_stat_context _ _ _ _ _ _ _ _ |- _ =>
    pose proof (task_stat_context_delay_safe environment critical saved_local sg frame
      TaskStatSampleWindow window_caller window_mask 10 (TaskStatAcquire TaskStatCapture) window_state X eq_refl Hcontext) as Hsafe;
    sep_apply_l_atomic (task_stat_delay_call_pre environment critical saved_local sg frame
      TaskStatSampleWindow window_caller window_mask 10 (TaskStatAcquire TaskStatCapture) window_state X eq_refl Hcontext)
  end.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_15 : OS_TaskStat_which_implies_wit_15.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint.
  apply task_stat_delay_post_context.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_16 : OS_TaskStat_which_implies_wit_16.
Proof.
  Unfold. left. intros.
  unfold task_stat_closed_checkpoint.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_17 : OS_TaskStat_which_implies_wit_17.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint; Intros.
  assert (Hnext : task_stat_context environment critical saved_local sg frame
    (task_stat_at TaskStatStack hook_caller hook_mask) hook_state X).
  { eapply task_stat_context_step; [eassumption|apply task_stat_step_hook]. }
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_18 : OS_TaskStat_which_implies_wit_18.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint; Intros.
  match goal with Hcontext : task_stat_context _ _ _ _ _ _ _ _ |- _ =>
    pose proof (proj2 (task_stat_context_current _ _ _ _ _ _ _ _ Hcontext)) as Hadmission;
    pose proof (task_stat_context_stack_safe environment critical saved_local sg frame
      hook_caller hook_mask hook_state X Hcontext) as Hsafe
  end.
  cbn [task_stat_call_admission task_stat_delay_instruction task_stat_at
    task_stat_stage task_stat_caller task_stat_mask] in Hadmission.
  assert (Hstack_configuration : task_stat_stk_chk_configuration sg).
  { match goal with H : task_stat_configuration sg |- _ =>
      exact (proj2 (proj2 H)) end. }
  rewrite time_dly_closed_inv_equiv.
  unfold Ucos2Verify.lib.ucos2_verify_inv.UCOS2_inv.
  entailer!.
Qed. 

Lemma proof_of_OS_TaskStat_which_implies_wit_19 : OS_TaskStat_which_implies_wit_19.
Proof.
  pre_process.
  unfold task_stat_closed_checkpoint.
  apply task_stat_stack_post_context.
Qed. 

