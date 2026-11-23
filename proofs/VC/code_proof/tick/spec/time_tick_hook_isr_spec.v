Require Export Ucos2Verify.VC.code.tick.spec.time_tick_fixed_hook_spec.
Require Export Ucos2Verify.VC.code.tick.spec.time_tick_signal_spec.
Require Export Ucos2Verify.VC.code.tick.spec.time_tick_hook_spec.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition time_tick_signal_entry sg (before : UCOS2_Verify_State) : Prop :=
  sg.(osKernelConfig).(cfgTimerEnabled) = true /\ sem_post_profile sg /\
  time_tick_post_readable sg before (time_tick_signal_pointer before) /\
  0 < os_sched_ints before.

Lemma time_tick_entry_signal_entry : forall sg invocation origin before,
  time_tick_entry sg invocation origin before -> time_tick_signal_entry sg before.
Proof.
  intros sg invocation origin before [Hcfg [_ [Hnest [_ Hread]]]].
  unfold time_tick_signal_entry, sem_post_profile; rewrite Hcfg.
  split; [reflexivity|split; [reflexivity|split; assumption]].
Qed.

Definition time_tick_hook_isr_post platform critical application sg invocation origin
  region_entry before app_value counter_address counter : Assertion :=
  EX counter_after after,
    coq_prop (time_tick_hook_result (time_tick_fixed_application sg application) sg
      app_value counter before app_value counter_after after) &&
    time_tick_owned platform critical (time_tick_fixed_application sg application) sg
      invocation origin region_entry app_value counter_address counter_after after.

Lemma time_tick_hook_isr_open : forall platform critical application sg invocation origin
  region_entry before app_value counter_address counter,
  time_tick_entry sg invocation origin before ->
  time_tick_owned platform critical (time_tick_fixed_application sg application) sg
    invocation origin region_entry app_value counter_address counter before |--
  coq_prop (time_tick_signal_entry sg before /\ event_table_layout_prop sg) &&
  (time_tick_sched_owned platform critical sg invocation origin region_entry before **
   application.(time_tick_application_own) app_value ** counter_address # UShort |-> counter).
Proof.
  intros; sep_apply (time_tick_fixed_owned_open platform critical sg application
    invocation origin region_entry app_value counter_address counter before).
  pose proof (time_tick_entry_signal_entry sg invocation origin before H) as Hentry.
  unfold time_tick_sched_owned; entailer!.
Qed.

Lemma time_tick_hook_isr_no_signal_return : forall platform critical application sg invocation origin
  region_entry before app_value counter_address counter,
  event_table_layout_prop sg -> time_tick_hook_advanced counter < 10 ->
  time_tick_sched_owned platform critical sg invocation origin region_entry before **
  application.(time_tick_application_own) app_value **
  counter_address # UShort |-> time_tick_hook_advanced counter |--
    time_tick_hook_isr_post platform critical application sg invocation origin
      region_entry before app_value counter_address counter.
Proof.
  intros platform critical application sg invocation origin region_entry before app_value
    counter_address counter Hlayout Htest.
  pose proof (time_tick_hook_no_signal_guard counter Htest) as Hsignal.
  pose proof (time_tick_fixed_hook_no_signal_result sg application app_value counter
    before Hsignal) as Hresult.
  pose proof (time_tick_hook_counter_after_no_signal counter Hsignal) as Hcounter.
  unfold time_tick_hook_counter_after in Hcounter.
  unfold time_tick_hook_isr_post; Exists (time_tick_hook_advanced counter) before.
  rewrite Hcounter in Hresult.
  unfold time_tick_owned, time_tick_fixed_application, time_tick_sched_owned.
  cbn [time_tick_application_own]; entailer!.
Qed.

Lemma time_tick_hook_isr_signal_return : forall platform critical application sg invocation origin
  region_entry before app_value counter_address counter error after,
  event_table_layout_prop sg -> 10 <= time_tick_hook_advanced counter ->
  time_tick_sem_result sg (time_tick_signal_pointer before) before error after ->
  time_tick_sched_owned platform critical sg invocation origin region_entry after **
  application.(time_tick_application_own) app_value ** counter_address # UShort |-> 0 |--
    time_tick_hook_isr_post platform critical application sg invocation origin
      region_entry before app_value counter_address counter.
Proof.
  intros platform critical application sg invocation origin region_entry before app_value
    counter_address counter error after Hlayout Htest [result [Herror Hpost]].
  pose proof (time_tick_hook_signal_guard counter Htest) as Hsignal.
  pose proof (time_tick_fixed_hook_signal_result sg application app_value counter
    before result after Hsignal Hpost) as Hresult.
  pose proof (time_tick_hook_counter_after_signal counter Hsignal) as Hcounter.
  unfold time_tick_hook_counter_after in Hcounter.
  unfold time_tick_hook_isr_post; Exists 0 after; rewrite Hcounter in Hresult.
  unfold time_tick_owned, time_tick_fixed_application, time_tick_sched_owned.
  cbn [time_tick_application_own]; entailer!.
Qed.
