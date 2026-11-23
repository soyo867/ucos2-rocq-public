Require Export Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.tick.spec.app_time_tick_hook_spec.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The pinned App body is empty. Its previous application owner is retained
    as a frame. The ISR caller also lends the compiled event layout and the
    readonly selector table; neither comes from the interrupt mask. *)
Definition time_tick_fixed_application (sg : StableGlobVars)
  (application : TimeTickApplicationResources) : TimeTickApplicationResources :=
  {| time_tick_application_own := fun value =>
       coq_prop (event_table_layout_prop sg) &&
       (application.(time_tick_application_own) value ** unmap_table_rep sg);
     time_tick_application_return := fun before log after => log = [] /\ after = before |}.

Lemma time_tick_fixed_app_return : forall sg application state after value,
  app_time_tick_hook_step sg state after ->
  after = state /\
  (time_tick_fixed_application sg application).(time_tick_application_return) value [] value.
Proof. intros; split; [exact H|split; reflexivity]. Qed.

Lemma time_tick_fixed_hook_no_signal_result : forall sg application app_value counter state,
  snd (time_tick_hook_counter_step counter) = false ->
  time_tick_hook_result (time_tick_fixed_application sg application) sg
    app_value counter state app_value (fst (time_tick_hook_counter_step counter)) state.
Proof.
  intros sg application app_value counter state Hsignal.
  exists [], state; split; [split; reflexivity|].
  split; [constructor|].
  split; [reflexivity|rewrite Hsignal; reflexivity].
Qed.

Lemma time_tick_fixed_hook_signal_result : forall sg application app_value counter
  state result after,
  snd (time_tick_hook_counter_step counter) = true ->
  time_tick_post_call sg state.(TimerState).(timerSignalSem) state result after ->
  time_tick_hook_result (time_tick_fixed_application sg application) sg
    app_value counter state app_value (fst (time_tick_hook_counter_step counter)) after.
Proof.
  intros sg application app_value counter state result after Hsignal Hpost.
  exists [], state; split; [split; reflexivity|].
  split; [constructor|].
  split; [reflexivity|rewrite Hsignal; exists result; exact Hpost].
Qed.

Lemma time_tick_fixed_owned_open : forall platform critical sg application invocation origin
  region_entry app_value counter_address counter state,
  time_tick_owned platform critical (time_tick_fixed_application sg application) sg
    invocation origin region_entry app_value counter_address counter state |--
  coq_prop (event_table_layout_prop sg) &&
  (interrupt_platform_running platform invocation origin 192 **
    critical_region_inside critical sg invocation region_entry **
    application.(time_tick_application_own) app_value **
    counter_address # UShort |-> counter ** UCOS2_inv sg state ** unmap_table_rep sg).
Proof.
  intros; unfold time_tick_owned, time_tick_fixed_application.
  cbn [time_tick_application_own]; entailer!.
Qed.

Lemma time_tick_fixed_owned_close : forall platform critical sg application invocation origin
  region_entry app_value counter_address counter state,
  event_table_layout_prop sg ->
  interrupt_platform_running platform invocation origin 192 **
    critical_region_inside critical sg invocation region_entry **
    application.(time_tick_application_own) app_value **
    counter_address # UShort |-> counter ** UCOS2_inv sg state ** unmap_table_rep sg |--
  time_tick_owned platform critical (time_tick_fixed_application sg application) sg
    invocation origin region_entry app_value counter_address counter state.
Proof.
  intros; unfold time_tick_owned, time_tick_fixed_application.
  cbn [time_tick_application_own]; entailer!.
Qed.
