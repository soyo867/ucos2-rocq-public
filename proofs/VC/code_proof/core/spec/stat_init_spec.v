Require Export Ucos2Verify.VC.code.time.spec.time_dly_spec.
Require Export Ucos2Verify.lib.statistics_execution.
Require Export Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.ucos2_state_machine.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.interrupt.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** False resets after Dly(2); true calibrates after Dly(100/10).
    A rejected delay still enters its phase. This is a proof index. *)
Definition stat_init_ticks (calibrate : bool) : Z := if calibrate then 10 else 2.
Definition stat_init_statistics_update (calibrate : bool) (stats : StatisticsState) :=
  if calibrate then statistics_calibrate stats else statistics_reset_counter stats.
Definition stat_init_update (calibrate : bool) (state : UCOS2_Verify_State) :=
  replace_StatsS (stat_init_statistics_update calibrate state.(StatsState)) state.

(** Retain OSTimeDly's actual caller receipt for the next Save. *)
Definition stat_init_delay_program environment critical sg caller mask ticks
  : program UCOS2_Verify_State TaskSuspendCaller :=
  time_dly_result environment critical sg caller mask ticks.
Definition stat_init_write_program (calibrate : bool) : program UCOS2_Verify_State unit :=
  fun acquired _ released => released = stat_init_update calibrate acquired.
Definition stat_init_protected_program environment critical sg caller mask calibrate
  : program UCOS2_Verify_State TaskSuspendCaller :=
  StateRelMonad.bind (task_suspend_save_program environment critical sg caller mask)
    (fun entered => StateRelMonad.bind (stat_init_write_program calibrate)
      (fun _ => task_suspend_restore_program environment critical sg (fst entered))).
Definition stat_init_phase_program environment critical sg caller mask calibrate
  : program UCOS2_Verify_State TaskSuspendCaller :=
  StateRelMonad.bind
    (stat_init_delay_program environment critical sg caller mask (stat_init_ticks calibrate))
    (fun delayed => stat_init_protected_program environment critical sg delayed mask calibrate).
Definition stat_init_program environment critical sg caller mask : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (stat_init_phase_program environment critical sg caller mask false)
    (fun checkpoint => StateRelMonad.bind
      (stat_init_phase_program environment critical sg checkpoint mask true)
      (fun _ => StateRelMonad.ret tt)).

(** Each phase retains its own saved word and acquired sample. Its
    protected write endpoint is distinct from the Restore endpoint. *)
Definition stat_init_phase_result environment critical sg caller mask calibrate before returned current : Prop :=
  exists delayed after_delay active saved acquired,
    time_dly_result environment critical sg caller mask (stat_init_ticks calibrate)
      before delayed after_delay /\
    task_suspend_save_effect environment critical sg delayed active mask saved after_delay acquired /\
    task_suspend_restore_effect environment critical sg active returned
      (stat_init_update calibrate acquired) current.
Definition stat_init_result environment critical sg caller mask before returned current : Prop :=
  exists checkpoint_call checkpoint,
    stat_init_phase_result environment critical sg caller mask false before checkpoint_call checkpoint /\
    stat_init_phase_result environment critical sg checkpoint_call mask true checkpoint returned current.

Lemma stat_init_delay_program_forget_iff : forall environment critical sg caller mask ticks before current,
  (exists returned, stat_init_delay_program environment critical sg caller mask ticks before returned current) <->
  time_dly_program environment critical sg caller mask ticks before tt current.
Proof.
  intros environment critical sg caller mask ticks before current; split.
  - intros [returned Hresult]; eapply time_dly_result_program; exact Hresult.
  - unfold time_dly_program, time_dly_prefix_program, time_dly_tail_program.
    intros [[scheduled middle] [checkpoint [[entry [entry_state [[Hentry Hstate] Hprefix]]] Htail]]].
    subst entry entry_state.
    destruct (time_dly_noop ticks before) eqn:Hnoop.
    + destruct Hprefix as [Hpair Hcheckpoint]; inversion Hpair; subst scheduled middle checkpoint.
      destruct Htail as [_ Hcurrent]; subst current.
      exists caller; unfold stat_init_delay_program, time_dly_result; rewrite Hnoop; auto.
    + destruct Hprefix as [entered [acquired [Hsave [u [released [Hwrite [next [endstate [Hrestore Hret]]]]]]]]].
      destruct Hret as [Hpair Hcheckpoint]; inversion Hpair; subst scheduled middle checkpoint.
      destruct Htail as [returned [after [Hschedule [_ Hcurrent]]]]; subst after.
      exists returned; unfold stat_init_delay_program, time_dly_result; rewrite Hnoop.
      exists next, endstate; split; [|exact Hschedule].
      unfold time_dly_prefix_program; exists before, before; split; [split; reflexivity|].
      rewrite Hnoop; exists entered, acquired; split; [exact Hsave|].
      exists u, released; split; [exact Hwrite|].
      exists next, endstate; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma stat_init_phase_result_program : forall environment critical sg caller mask calibrate before returned current,
  stat_init_phase_result environment critical sg caller mask calibrate before returned current <->
  stat_init_phase_program environment critical sg caller mask calibrate before returned current.
Proof.
  intros; unfold stat_init_phase_result, stat_init_phase_program,
    stat_init_protected_program, stat_init_write_program, stat_init_delay_program,
    task_suspend_save_program, task_suspend_restore_program; split.
  - intros [delayed [after_delay [active [saved [acquired [Hd [Hs Hr]]]]]]].
    exists delayed, after_delay; split; [exact Hd|].
    exists (active, saved), acquired; split; [exact Hs|].
    exists tt, (stat_init_update calibrate acquired); split; [reflexivity|exact Hr].
  - intros [delayed [after_delay [Hd [[active saved] [acquired [Hs [u [released [-> Hr]]]]]]]]].
    exists delayed, after_delay, active, saved, acquired; auto.
Qed.

Lemma stat_init_result_program : forall environment critical sg caller mask before returned current,
  stat_init_result environment critical sg caller mask before returned current ->
  stat_init_program environment critical sg caller mask before tt current.
Proof.
  intros environment critical sg caller mask before returned current
    [checkpoint_call [checkpoint [Hreset Hcalibrate]]].
  unfold stat_init_program; exists checkpoint_call, checkpoint; split.
  - apply stat_init_phase_result_program; exact Hreset.
  - exists returned, current; split.
    + apply stat_init_phase_result_program; exact Hcalibrate.
    + split; reflexivity.
Qed.

(** The protocol concerns the two actual Dly call endpoints. No-op branches
    impose no task-ready/clean-Pend condition. No eventual return is assumed. *)
Definition stat_init_call_protocol environment critical sg caller mask before : Prop :=
  time_dly_entry_facts environment critical sg caller mask 2 before /\
  forall checkpoint_call checkpoint,
    stat_init_phase_result environment critical sg caller mask false before checkpoint_call checkpoint ->
    time_dly_entry_facts environment critical sg checkpoint_call mask 10 checkpoint.
Definition stat_init_safe environment critical sg caller mask before
  (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before) (stat_init_program environment critical sg caller mask) X.
Definition stat_init_after_phase_program environment critical sg mask (calibrate : bool) caller
  : program UCOS2_Verify_State unit :=
  if calibrate then StateRelMonad.ret tt else
    StateRelMonad.bind (stat_init_phase_program environment critical sg caller mask true)
      (fun _ => StateRelMonad.ret tt).
Definition stat_init_remaining_program environment critical sg caller mask calibrate
  : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (stat_init_phase_program environment critical sg caller mask calibrate)
    (stat_init_after_phase_program environment critical sg mask calibrate).
Definition stat_init_delay_continuation environment critical sg caller mask calibrate before
  (X : unit -> UCOS2_Verify_State -> Prop) : unit -> UCOS2_Verify_State -> Prop :=
  fun _ current => forall returned,
    time_dly_result environment critical sg caller mask (stat_init_ticks calibrate) before returned current ->
    safeExec (fun state => state = current)
      (StateRelMonad.bind (stat_init_protected_program environment critical sg returned mask calibrate)
        (stat_init_after_phase_program environment critical sg mask calibrate)) X.

Lemma stat_init_delay_safe : forall environment critical sg caller mask calibrate before X,
  safeExec (fun state => state = before)
    (stat_init_remaining_program environment critical sg caller mask calibrate) X ->
  time_dly_safe environment critical sg caller mask (stat_init_ticks calibrate) before
    (stat_init_delay_continuation environment critical sg caller mask calibrate before X).
Proof.
  intros environment critical sg caller mask calibrate before X [start [-> Hsafe]].
  exists before; split; [reflexivity|].
  intros u current Hd returned Hresult.
  exists current; split; [reflexivity|].
  intros result final [out [after [Hp Htail]]].
  apply (Hsafe result final).
  exists out, after; split; [|exact Htail].
  exists returned, current; split; assumption.
Qed.

Definition stat_init_prefix environment critical sg original mask initial (calibrate : bool) caller before : Prop :=
  if calibrate then stat_init_phase_result environment critical sg original mask false initial caller before
  else caller = original /\ before = initial.
Definition stat_init_phase_facts environment critical sg original mask initial calibrate caller before X : Prop :=
  stat_init_call_protocol environment critical sg original mask initial /\
  stat_init_safe environment critical sg original mask initial X /\
  stat_init_prefix environment critical sg original mask initial calibrate caller before.

Lemma stat_init_phase_safe : forall environment critical sg original mask initial calibrate caller before X,
  stat_init_phase_facts environment critical sg original mask initial calibrate caller before X ->
  safeExec (fun state => state = before)
    (stat_init_remaining_program environment critical sg caller mask calibrate) X.
Proof.
  intros environment critical sg original mask initial [] caller before X [Hprotocol [Hsafe Hprefix]].
  - cbn [stat_init_remaining_program stat_init_after_phase_program].
    eapply (highstepbind_derive (stat_init_phase_program environment critical sg original mask false)
      (fun checkpoint => StateRelMonad.bind
        (stat_init_phase_program environment critical sg checkpoint mask true)
        (fun _ => StateRelMonad.ret tt))
      (fun state => state = initial) caller (fun state => state = before)).
    + intros state ->; exists before; split; [apply stat_init_phase_result_program; exact Hprefix|reflexivity].
    + exact Hsafe.
  - destruct Hprefix as [-> ->]; exact Hsafe.
Qed.

Lemma stat_init_phase_entry : forall environment critical sg original mask initial calibrate caller before X,
  stat_init_phase_facts environment critical sg original mask initial calibrate caller before X ->
  time_dly_entry_facts environment critical sg caller mask (stat_init_ticks calibrate) before.
Proof.
  intros environment critical sg original mask initial [] caller before X [Hprotocol [Hsafe Hprefix]].
  - exact (proj2 Hprotocol caller before Hprefix).
  - destruct Hprefix as [-> ->]; exact (proj1 Hprotocol).
Qed.

Lemma stat_init_safe_return : forall environment critical sg caller mask before returned current X,
  stat_init_result environment critical sg caller mask before returned current ->
  stat_init_safe environment critical sg caller mask before X -> time_dly_return_safe current X.
Proof.
  intros environment critical sg caller mask before returned current X Hresult [start [-> Hsafe]].
  exists current; split; [reflexivity|].
  intros result final [-> ->]; apply Hsafe; eapply stat_init_result_program; exact Hresult.
Qed.

Definition stat_init_call_post environment critical saved_local sg caller mask before frame X : Assertion :=
  EX returned current,
    coq_prop (stat_init_result environment critical sg caller mask before returned current /\
      time_dly_return_safe current X) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).
Definition stat_init_config (sg : StableGlobVars) : Prop :=
  valid_stable_glob_vars sg /\ sg.(osKernelConfig).(cfgStatisticsEnabled) = true.
Definition stat_init_addresses sg counter maximum ready : Prop :=
  counter = sg.(g_OSIdleCtr) /\ maximum = sg.(g_OSIdleCtrMax) /\ ready = sg.(g_OSStatRdy).
Definition stat_init_ready_byte (stats : StatisticsState) : Z := if stats.(statReady) then 1 else 0.

Definition stat_init_protected_safe environment critical sg caller mask calibrate before X : Prop :=
  safeExec (fun state => state = before)
    (StateRelMonad.bind (stat_init_protected_program environment critical sg caller mask calibrate)
      (stat_init_after_phase_program environment critical sg mask calibrate)) X.

Lemma stat_init_delay_return_continuation : forall environment critical sg caller mask calibrate before
  returned current X,
  time_dly_return_safe current
    (stat_init_delay_continuation environment critical sg caller mask calibrate before X) ->
  time_dly_result environment critical sg caller mask (stat_init_ticks calibrate) before returned current ->
  stat_init_protected_safe environment critical sg returned mask calibrate current X.
Proof.
  intros environment critical sg caller mask calibrate before returned current X [start [-> Hsafe]] Hresult.
  apply (Hsafe tt current); [split; reflexivity|exact Hresult].
Qed.

Definition stat_init_delayed_facts environment critical sg original mask initial calibrate caller before
  delayed after_delay X : Prop :=
  stat_init_phase_facts environment critical sg original mask initial calibrate caller before X /\
  time_dly_result environment critical sg caller mask (stat_init_ticks calibrate) before delayed after_delay /\
  stat_init_protected_safe environment critical sg delayed mask calibrate after_delay X.

Definition stat_init_acquired_facts environment critical sg original mask initial calibrate caller before
  delayed after_delay active saved acquired X : Prop :=
  stat_init_delayed_facts environment critical sg original mask initial calibrate caller before
    delayed after_delay X /\
  task_suspend_save_observation critical sg delayed active mask saved after_delay acquired /\
  task_suspend_save_effect environment critical sg delayed active mask saved after_delay acquired /\
  armv7a_irq_fiq_mask saved = mask /\ UCOS2_state_inv sg acquired.

Lemma stat_init_save_observation_mask : forall critical sg caller active mask saved before acquired,
  task_suspend_save_observation critical sg caller active mask saved before acquired ->
  armv7a_irq_fiq_mask saved = mask.
Proof.
  intros critical sg [] [] mask saved before acquired;
    unfold task_suspend_save_observation, interrupt_saved_value; tauto.
Qed.

Lemma stat_init_acquired_phase_result : forall environment critical sg original mask initial calibrate
  caller before delayed after_delay active saved acquired returned current X,
  stat_init_acquired_facts environment critical sg original mask initial calibrate caller before
    delayed after_delay active saved acquired X ->
  task_suspend_restore_effect environment critical sg active returned
    (stat_init_update calibrate acquired) current ->
  stat_init_phase_result environment critical sg caller mask calibrate before returned current.
Proof.
  intros environment critical sg original mask initial calibrate caller before delayed after_delay
    active saved acquired returned current X [[Hphase [Hd Hsafe]] [Hobs [Hs Hrest]]] Hr.
  exists delayed, after_delay, active, saved, acquired; auto.
Qed.

Lemma stat_init_reset_next_phase : forall environment critical sg original mask initial
  delayed after_delay active saved acquired returned current X,
  stat_init_acquired_facts environment critical sg original mask initial false original initial
    delayed after_delay active saved acquired X ->
  task_suspend_restore_effect environment critical sg active returned
    (stat_init_update false acquired) current ->
  stat_init_phase_facts environment critical sg original mask initial true returned current X.
Proof.
  intros environment critical sg original mask initial delayed after_delay active saved acquired
    returned current X Hfacts Hr.
  pose proof (stat_init_acquired_phase_result environment critical sg original mask initial false
    original initial delayed after_delay active saved acquired returned current X Hfacts Hr) as Hphase.
  destruct Hfacts as [[[Hprotocol [Hsafe Hprefix]] Hdelay] Hacquired].
  split; [exact Hprotocol|]; split; assumption.
Qed.

Lemma stat_init_protected_return_safe : forall environment critical sg caller mask before active saved
  acquired returned current X,
  stat_init_protected_safe environment critical sg caller mask true before X ->
  task_suspend_save_effect environment critical sg caller active mask saved before acquired ->
  task_suspend_restore_effect environment critical sg active returned
    (stat_init_update true acquired) current ->
  time_dly_return_safe current X.
Proof.
  intros environment critical sg caller mask before active saved acquired returned current X
    [start [-> Hsafe]] Hsave Hrestore.
  exists current; split; [reflexivity|].
  intros result final [Hresult Hfinal]; subst result final; apply (Hsafe tt current).
  exists returned, current; split; [|split; reflexivity].
  exists (active, saved), acquired; split; [exact Hsave|].
  exists tt, (stat_init_update true acquired); split; [reflexivity|exact Hrestore].
Qed.

Lemma stat_init_calibration_return : forall environment critical sg original mask initial caller before
  delayed after_delay active saved acquired returned current X,
  stat_init_acquired_facts environment critical sg original mask initial true caller before
    delayed after_delay active saved acquired X ->
  task_suspend_restore_effect environment critical sg active returned
    (stat_init_update true acquired) current ->
  stat_init_result environment critical sg original mask initial returned current /\
    time_dly_return_safe current X.
Proof.
  intros environment critical sg original mask initial caller before delayed after_delay active saved
    acquired returned current X Hfacts Hr.
  pose proof (stat_init_acquired_phase_result environment critical sg original mask initial true
    caller before delayed after_delay active saved acquired returned current X Hfacts Hr) as Hphase.
  destruct Hfacts as [[[Hprotocol [Hsafe Hprefix]] [Hd Hcontinuation]] [Hobs [Hs Hrest]]].
  split.
  - exists caller, before; split; assumption.
  - eapply stat_init_protected_return_safe; eassumption.
Qed.

Lemma stat_init_update_preserves_validity : forall sg calibrate state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true -> UCOS2_state_inv sg state ->
  UCOS2_state_inv sg (stat_init_update calibrate state).
Proof.
  intros sg [] state Hcfg Hvalid.
  - exact (selected_transition_valid _ _ _ (statistics_calibrate_selected_transition sg Hcfg)
      state (stat_init_update true state) Hvalid eq_refl).
  - exact (selected_transition_valid _ _ _ (statistics_reset_selected_transition sg Hcfg)
      state (stat_init_update false state) Hvalid eq_refl).
Qed.

Lemma stat_init_call_resources_update_eq : forall environment saved_local sg caller calibrate state,
  task_suspend_call_resources environment saved_local sg caller (stat_init_update calibrate state) =
  task_suspend_call_resources environment saved_local sg caller state.
Proof. intros; destruct caller; reflexivity. Qed.
Lemma stat_init_update_source_preserved : forall call calibrate state,
  task_tcb_init_stack_source_preserved call state (stat_init_update calibrate state).
Proof. intros; unfold task_tcb_init_stack_source_preserved; exact (fun H => H). Qed.
Lemma stat_init_update_call_preserved : forall sg invocation calibrate state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_tcb_init_call_preserved sg invocation state (stat_init_update calibrate state).
Proof.
  intros sg invocation calibrate state Hcfg Hvalid; split.
  - apply stat_init_update_preserves_validity; assumption.
  - split; [unfold task_creation_frame; reflexivity|]. split; [auto|reflexivity].
Qed.

(** The residual and caller resources depend on no Stats projection.
    The acquisition token stays indexed by acquired through both stores. *)
Definition stat_init_statistics_frame environment critical saved_local sg active saved acquired : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    (task_suspend_view active).(os_execution_invocation)
    (task_suspend_view active).(os_execution_origin) saved acquired **
  UCOS2_raw_rep_missing_statistics sg acquired **
  task_suspend_call_resources environment saved_local sg active acquired.
Lemma stat_init_masked_split_statistics : forall environment critical saved_local sg active saved acquired,
  task_suspend_masked environment critical saved_local sg active saved acquired acquired --||--
  coq_prop (UCOS2_state_inv sg acquired) &&
  (statistics_rep sg acquired.(StatsState) **
    stat_init_statistics_frame environment critical saved_local sg active saved acquired).
Proof.
  intros; unfold task_suspend_masked, stat_init_statistics_frame;
    rewrite UCOS2_inv_split_statistics; split; entailer!.
Qed.
Lemma stat_init_masked_merge_statistics : forall environment critical saved_local sg active saved acquired calibrate,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true -> UCOS2_state_inv sg acquired ->
  statistics_rep sg (stat_init_statistics_update calibrate acquired.(StatsState)) **
    stat_init_statistics_frame environment critical saved_local sg active saved acquired |--
  task_suspend_masked environment critical saved_local sg active saved acquired (stat_init_update calibrate acquired).
Proof.
  intros environment critical saved_local sg active saved acquired calibrate Hcfg Hvalid.
  unfold task_suspend_masked; rewrite stat_init_call_resources_update_eq.
  unfold stat_init_statistics_frame.
  assert (Hmerge : statistics_rep sg (stat_init_statistics_update calibrate acquired.(StatsState)) **
    UCOS2_raw_rep_missing_statistics sg acquired |-- UCOS2_inv sg (stat_init_update calibrate acquired)).
  { apply (UCOS2_inv_merge_updated_module sg acquired (stat_init_update calibrate acquired) StatisticsModule).
    - apply stat_init_update_preserves_validity; assumption.
    - unfold UCOS2_raw_rep_missing_module, UCOS2_raw_rep_missing_statistics, stat_init_update, replace_StatsS.
      entailer!. }
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Definition stat_init_reset_residual sg (state : StatisticsState) : Assertion :=
  sg.(g_OSIdleCtrMax) # UInt |-> state.(idleCtrMax) **
  sg.(g_OSIdleCtrRun) # UInt |-> state.(idleCtrRun) **
  sg.(g_OSCPUUsage) # UChar |-> state.(cpuUsage) **
  sg.(g_OSStatRdy) # UChar |-> (if state.(statReady) then 1 else 0).
Definition stat_init_calibration_residual sg (state : StatisticsState) : Assertion :=
  sg.(g_OSIdleCtrRun) # UInt |-> state.(idleCtrRun) **
  sg.(g_OSCPUUsage) # UChar |-> state.(cpuUsage).
Lemma stat_init_reset_split : forall sg stats,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_rep sg stats --||--
  (sg.(g_OSIdleCtr) # UInt |-> stats.(idleCtr) ** stat_init_reset_residual sg stats).
Proof. intros; unfold statistics_rep, stat_init_reset_residual; rewrite H; split; entailer!. Qed.
Lemma stat_init_reset_merge : forall sg stats,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  sg.(g_OSIdleCtr) # UInt |-> 0 ** stat_init_reset_residual sg stats |--
  statistics_rep sg (statistics_reset_counter stats).
Proof.
  intros; unfold statistics_rep, stat_init_reset_residual, statistics_reset_counter,
    statistics_set_counter; rewrite H; cbn [kernel_u32]; entailer!.
Qed.
Lemma stat_init_calibration_split : forall sg stats,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_rep sg stats --||--
  (sg.(g_OSIdleCtr) # UInt |-> stats.(idleCtr) **
   sg.(g_OSIdleCtrMax) # UInt |-> stats.(idleCtrMax) **
   sg.(g_OSStatRdy) # UChar |-> (if stats.(statReady) then 1 else 0) **
   stat_init_calibration_residual sg stats).
Proof. intros; unfold statistics_rep, stat_init_calibration_residual; rewrite H; split; entailer!. Qed.
Lemma stat_init_calibration_merge : forall sg stats,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  sg.(g_OSIdleCtr) # UInt |-> stats.(idleCtr) **
  sg.(g_OSIdleCtrMax) # UInt |-> stats.(idleCtr) **
  sg.(g_OSStatRdy) # UChar |-> 1 ** stat_init_calibration_residual sg stats |--
  statistics_rep sg (statistics_calibrate stats).
Proof.
  intros; unfold statistics_rep, stat_init_calibration_residual, statistics_calibrate;
    rewrite H; simpl; entailer!.
Qed.
