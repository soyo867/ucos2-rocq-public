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
From Ucos2Verify.VC.code.core Require Import stat_init_goal.
From Ucos2Verify.VC.code.core Require Import stat_init_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.core.spec.stat_init_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSStatInit_entail_wit_1 : OSStatInit_entail_wit_1.
Proof.
  right; intros.
  unfold time_dly_call_post at 1; Intros delayed1 after_delay1.
  assert (Hresult : time_dly_result environment critical sg original mask 2
      initial delayed1 after_delay1) by tauto.
  assert (Hreturn : time_dly_return_safe after_delay1
      (stat_init_delay_continuation environment critical sg original mask false initial X))
    by tauto.
  pose proof (stat_init_delay_return_continuation environment critical sg original mask false
    initial delayed1 after_delay1 X Hreturn Hresult) as Hprotected.
  Exists delayed1 after_delay1.
  unfold stat_init_delayed_facts.
  entailer!.
Qed.
Lemma proof_of_OSStatInit_entail_wit_2 : OSStatInit_entail_wit_2.
Proof.
  right; intros.
  unfold task_suspend_save_history_post; Intros active1 acquired1.
  assert (Hobservation : task_suspend_save_observation critical sg delayed1 active1
      mask retval after_delay1 acquired1) by tauto.
  assert (Hsave : task_suspend_save_effect environment critical sg delayed1 active1
      mask retval after_delay1 acquired1) by tauto.
  assert (Hmask : armv7a_irq_fiq_mask retval = mask).
  { exact (stat_init_save_observation_mask critical sg delayed1 active1 mask retval
      after_delay1 acquired1 Hobservation). }
  rewrite (stat_init_masked_split_statistics environment critical saved_local
    sg active1 retval acquired1).
  Intros.
  assert (Hcfg : sg.(osKernelConfig).(cfgStatisticsEnabled) = true).
  { unfold stat_init_config in PreH1; tauto. }
  pose proof (stat_init_reset_split sg (StatsState acquired1) Hcfg) as Hsplit.
  pose proof PreH2 as Haddresses.
  unfold stat_init_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmax Hready]].
  rewrite <- Hcounter in Hsplit.
  rewrite Hsplit.
  Exists active1 acquired1.
  unfold stat_init_acquired_facts.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_entail_wit_3 : OSStatInit_entail_wit_3.
Proof.
  left; intros.
  assert (Hcfg : sg.(osKernelConfig).(cfgStatisticsEnabled) = true).
  { unfold stat_init_config in PreH1; tauto. }
  assert (Hvalid : UCOS2_state_inv sg acquired1).
  { unfold stat_init_acquired_facts in PreH4; tauto. }
  pose proof (stat_init_reset_merge sg (StatsState acquired1) Hcfg) as Hmerge.
  pose proof PreH2 as Haddresses.
  unfold stat_init_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmax Hready]].
  rewrite <- Hcounter in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof (stat_init_masked_merge_statistics environment critical saved_local
    sg active1 cpu_sr acquired1 false Hcfg Hvalid) as Hmasked.
  cbn [stat_init_statistics_update] in Hmasked.
  sep_apply_l_atomic Hmasked.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_entail_wit_4 : OSStatInit_entail_wit_4.
Proof.
  right; intros.
  unfold task_suspend_restore_history_post; Intros caller2 before2.
  assert (Hrestore : task_suspend_restore_effect environment critical sg active1 caller2
      (stat_init_update false acquired1) before2) by tauto.
  assert (Hphase : stat_init_phase_facts environment critical sg original mask initial
      true caller2 before2 X).
  { eapply stat_init_reset_next_phase; [exact PreH4 | exact Hrestore]. }
  assert (Hmask : armv7a_irq_fiq_mask cpu_sr = mask).
  { unfold stat_init_acquired_facts in PreH4; tauto. }
  rewrite Hmask.
  Exists caller2 before2.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_entail_wit_5 : OSStatInit_entail_wit_5.
Proof.
  right; intros.
  unfold time_dly_call_post at 1; Intros delayed2 after_delay2.
  assert (Hresult : time_dly_result environment critical sg caller2 mask 10
      before2 delayed2 after_delay2) by tauto.
  assert (Hreturn : time_dly_return_safe after_delay2
      (stat_init_delay_continuation environment critical sg caller2 mask true before2 X))
    by tauto.
  pose proof (stat_init_delay_return_continuation environment critical sg caller2 mask true
    before2 delayed2 after_delay2 X Hreturn Hresult) as Hprotected.
  Exists delayed2 after_delay2.
  unfold stat_init_delayed_facts.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_entail_wit_6 : OSStatInit_entail_wit_6.
Proof.
  right; intros.
  unfold task_suspend_save_history_post; Intros active2 acquired2.
  assert (Hobservation : task_suspend_save_observation critical sg delayed2 active2
      mask retval after_delay2 acquired2) by tauto.
  assert (Hsave : task_suspend_save_effect environment critical sg delayed2 active2
      mask retval after_delay2 acquired2) by tauto.
  assert (Hmask : armv7a_irq_fiq_mask retval = mask).
  { exact (stat_init_save_observation_mask critical sg delayed2 active2 mask retval
      after_delay2 acquired2 Hobservation). }
  rewrite (stat_init_masked_split_statistics environment critical saved_local
    sg active2 retval acquired2).
  Intros.
  assert (Hcfg : sg.(osKernelConfig).(cfgStatisticsEnabled) = true).
  { unfold stat_init_config in PreH1; tauto. }
  pose proof (stat_init_calibration_split sg (StatsState acquired2) Hcfg) as Hsplit.
  pose proof PreH2 as Haddresses.
  unfold stat_init_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmax Hready]].
  rewrite <- Hcounter, <- Hmax, <- Hready in Hsplit.
  rewrite Hsplit.
  Exists active2 acquired2.
  unfold stat_init_acquired_facts.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_entail_wit_7 : OSStatInit_entail_wit_7.
Proof.
  left; intros.
  assert (Hcfg : sg.(osKernelConfig).(cfgStatisticsEnabled) = true).
  { unfold stat_init_config in PreH1; tauto. }
  assert (Hvalid : UCOS2_state_inv sg acquired2).
  { unfold stat_init_acquired_facts in PreH4; tauto. }
  pose proof (stat_init_calibration_merge sg (StatsState acquired2) Hcfg) as Hmerge.
  pose proof PreH2 as Haddresses.
  unfold stat_init_addresses in Haddresses.
  destruct Haddresses as [Hcounter [Hmax Hready]].
  rewrite <- Hcounter, <- Hmax, <- Hready in Hmerge.
  sep_apply_l_atomic Hmerge.
  pose proof (stat_init_masked_merge_statistics environment critical saved_local
    sg active2 cpu_sr acquired2 true Hcfg Hvalid) as Hmasked.
  cbn [stat_init_statistics_update] in Hmasked.
  sep_apply_l_atomic Hmasked.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_entail_wit_8 : OSStatInit_entail_wit_8.
Proof.
  right; intros.
  unfold task_suspend_restore_history_post; Intros returned current.
  assert (Hrestore : task_suspend_restore_effect environment critical sg active2 returned
      (stat_init_update true acquired2) current) by tauto.
  pose proof (stat_init_calibration_return environment critical sg original mask initial
    caller2 before2 delayed2 after_delay2 active2 cpu_sr acquired2 returned current X
    PreH4 Hrestore) as [Hresult Hreturn].
  assert (Hmask : armv7a_irq_fiq_mask cpu_sr = mask).
  { unfold stat_init_acquired_facts in PreH4; tauto. }
  rewrite Hmask.
  unfold stat_init_call_post.
  Exists returned current.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_which_implies_wit_1 : OSStatInit_which_implies_wit_1.
Proof.
  right; intros.
  pose proof (stat_init_phase_safe environment critical sg original mask initial false
    original initial X PreH1) as Hphase_safe.
  pose proof (stat_init_delay_safe environment critical sg original mask false initial X
    Hphase_safe) as Htime_safe.
  pose proof (stat_init_phase_entry environment critical sg original mask initial false
    original initial X PreH1) as Hentry.
  unfold time_dly_call_pre.
  entailer!.
Qed.

Lemma proof_of_OSStatInit_which_implies_wit_2 : OSStatInit_which_implies_wit_2.
Proof.
  right; intros.
  pose proof (stat_init_phase_safe environment critical sg original mask initial true
    caller2 before2 X PreH1) as Hphase_safe.
  pose proof (stat_init_delay_safe environment critical sg caller2 mask true before2 X
    Hphase_safe) as Htime_safe.
  pose proof (stat_init_phase_entry environment critical sg original mask initial true
    caller2 before2 X PreH1) as Hentry.
  unfold time_dly_call_pre.
  entailer!.
Qed.

