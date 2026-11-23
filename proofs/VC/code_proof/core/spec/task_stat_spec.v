Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Ucos2Verify.lib.statistics Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_state_machine.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stk_chk_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.lib.statistics.
Require Export Ucos2Verify.lib.statistics_execution.
Require Export Ucos2Verify.VC.code.time.spec.time_dly_spec.
Require Export Ucos2Verify.VC.code.core.spec.task_stat_stk_chk_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stat_hook_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_program_storage.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source instructions, finite prefixes and current-caller continuations
    for the selected repaired OS_TaskStat source.  An outside/raw equality
    supplies a reversible view of ONE owned heap; environment intervals
    are represented separately by [task_stat_step_interference].  Callee
    admissions remain the actual existing entry requirements. *)

Definition task_stat_set_usage (state : StatisticsState) (usage : Z) : StatisticsState :=
  {| idleCtr := state.(idleCtr); idleCtrMax := state.(idleCtrMax);
     idleCtrRun := state.(idleCtrRun); cpuUsage := usage; statReady := state.(statReady) |}.

Definition task_stat_set_calibration (state : StatisticsState) (calibration : Z) : StatisticsState :=
  {| idleCtr := state.(idleCtr); idleCtrMax := calibration;
     idleCtrRun := state.(idleCtrRun); cpuUsage := state.(cpuUsage); statReady := state.(statReady) |}.

Definition task_stat_initial_counter (state : StatisticsState) : StatisticsState :=
  statistics_set_counter state (state.(idleCtrMax) * 100).

Definition task_stat_sample_usage (sample : StatisticsSample) : Z :=
  if Z.eqb sample.(sampleDivisor) 0 then 0 else
  let ratio := sample.(sampleRun) / sample.(sampleDivisor) in
  if ratio <=? 100 then 100 - ratio else 0.

Definition task_stat_needs_recalibration (sample : StatisticsSample) : bool :=
  andb (negb (Z.eqb sample.(sampleDivisor) 0))
    (negb (sample.(sampleRun) / sample.(sampleDivisor) <=? 100)).

Lemma task_stat_set_usage_preserves_validity : forall state usage,
  valid_statistics_state state -> 0 <= usage < 256 ->
  valid_statistics_state (task_stat_set_usage state usage).
Proof. intros state usage Hstate Husage; unfold valid_statistics_state, task_stat_set_usage in *; cbn; tauto. Qed.

Lemma task_stat_set_calibration_preserves_validity : forall state calibration,
  valid_statistics_state state -> 0 <= calibration < 4294967296 ->
  valid_statistics_state (task_stat_set_calibration state calibration).
Proof. intros state calibration Hstate Hcalibration; unfold valid_statistics_state, task_stat_set_calibration in *; cbn; tauto. Qed.

Lemma task_stat_initial_counter_preserves_validity : forall state,
  valid_statistics_state state -> valid_statistics_state (task_stat_initial_counter state).
Proof. intros; apply statistics_set_counter_preserves_validity; assumption. Qed.

Lemma task_stat_sample_usage_in_range : forall sample,
  valid_statistics_sample sample -> 0 <= task_stat_sample_usage sample <= 100.
Proof.
  intros sample [Hrun Hdivisor]; unfold task_stat_sample_usage.
  destruct (Z.eqb (sampleDivisor sample) 0) eqn:Hzero; [lia|].
  apply Z.eqb_neq in Hzero.
  assert (Hratio : 0 <= sampleRun sample / sampleDivisor sample) by (apply Z.div_pos; lia).
  destruct (sampleRun sample / sampleDivisor sample <=? 100) eqn:Hratio100; [|lia].
  apply Z.leb_le in Hratio100; lia.
Qed.

Lemma task_stat_sample_usage_repaired_eq : forall sample state,
  valid_statistics_sample sample ->
  task_stat_sample_usage sample = (statistics_repaired_update sample state).(cpuUsage).
Proof.
  intros sample state Hsample; unfold task_stat_sample_usage, statistics_repaired_update; cbn.
  destruct (Z.eqb (sampleDivisor sample) 0) eqn:Hzero; [reflexivity|].
  destruct (sampleRun sample / sampleDivisor sample <=? 100) eqn:Hratio; [|reflexivity].
  destruct Hsample as [Hrun Hdivisor]; apply Z.eqb_neq in Hzero; apply Z.leb_le in Hratio.
  assert (Hnonnegative : 0 <= sampleRun sample / sampleDivisor sample) by (apply Z.div_pos; lia).
  symmetry; apply kernel_u8_identity.
  change (0 <= 100 - sampleRun sample / sampleDivisor sample < 256); lia.
Qed.

(** Algebra for adjacent stores ONLY. A real environment interval between
    them must retain its own endpoint and physical heap; see the separate
    single-field updater and the non-atomic example below. *)
Lemma task_stat_sample_adjacent_stores_eq : forall sample state,
  valid_statistics_sample sample ->
  (if task_stat_needs_recalibration sample then
     task_stat_set_calibration (task_stat_set_usage state (task_stat_sample_usage sample))
       (sample.(sampleRun) / 100)
   else task_stat_set_usage state (task_stat_sample_usage sample)) =
  statistics_repaired_update sample state.
Proof.
  intros sample state Hsample.
  rewrite (task_stat_sample_usage_repaired_eq sample state Hsample).
  unfold task_stat_needs_recalibration, task_stat_set_usage, task_stat_set_calibration,
    statistics_repaired_update; cbn.
  destruct (Z.eqb (sampleDivisor sample) 0),
    (sampleRun sample / sampleDivisor sample <=? 100); reflexivity.
Qed.

Lemma task_stat_recalibration_positive : forall sample,
  valid_statistics_sample sample -> task_stat_needs_recalibration sample = true ->
  0 < sample.(sampleRun) / 100.
Proof.
  intros sample [Hrun Hdivisor] Hneeded; unfold task_stat_needs_recalibration in Hneeded.
  apply Bool.andb_true_iff in Hneeded; destruct Hneeded as [Hnonzero Hratio].
  apply Bool.negb_true_iff in Hnonzero; apply Z.eqb_neq in Hnonzero.
  apply Bool.negb_true_iff in Hratio; apply Z.leb_gt in Hratio.
  assert (Hlarge : 100 <= sampleRun sample).
  { destruct (Z_le_gt_dec 100 (sampleRun sample)); [assumption|].
    assert (Hbound : sampleRun sample / sampleDivisor sample <= 100).
    { apply Z.div_le_upper_bound; nia. }
    lia. }
  apply Z.div_str_pos; lia.
Qed.

Lemma task_stat_small_initial_calibration_zero : forall state,
  0 <= state.(idleCtrMax) < 100 ->
  (statistics_scale_divisor state).(idleCtrMax) = 0.
Proof. intros state Hmax; cbn [statistics_scale_divisor]; apply Z.div_small; exact Hmax. Qed.

Lemma task_stat_initial_counter_uint : forall state,
  (task_stat_initial_counter state).(idleCtr) =
  unsigned_last_nbits (state.(idleCtrMax) * 100) 32.
Proof. intros; reflexivity. Qed.

Lemma task_stat_initial_counter_wrap_example :
  (task_stat_initial_counter (task_stat_set_calibration statistics_initial 42949673)).(idleCtr) = 4.
Proof. reflexivity. Qed.

Lemma task_stat_ratio_100_usage :
  task_stat_sample_usage {| sampleRun := 100; sampleDivisor := 1 |} = 0 /\
  task_stat_needs_recalibration {| sampleRun := 100; sampleDivisor := 1 |} = false.
Proof. split; reflexivity. Qed.

Lemma task_stat_ratio_101_recalibrates :
  task_stat_sample_usage {| sampleRun := 101; sampleDivisor := 1 |} = 0 /\
  task_stat_needs_recalibration {| sampleRun := 101; sampleDivisor := 1 |} = true.
Proof. split; reflexivity. Qed.

Lemma task_stat_captured_zero_usage : forall run,
  task_stat_sample_usage {| sampleRun := run; sampleDivisor := 0 |} = 0 /\
  task_stat_needs_recalibration {| sampleRun := run; sampleDivisor := 0 |} = false.
Proof. intros; split; reflexivity. Qed.

Lemma task_stat_maximal_sample_recalibrates :
  task_stat_sample_usage {| sampleRun := 4294967295; sampleDivisor := 1 |} = 0 /\
  4294967295 / 100 = 42949672.
Proof. split; reflexivity. Qed.

(** Updating calibration after interference preserves the usage in that
    actual later state. Replacing the whole sequence by the two-field
    repaired transformer would lose this permitted distinction. *)
Lemma task_stat_separate_store_usage_example :
  (task_stat_set_calibration
     (task_stat_set_usage statistics_initial 37) (101 / 100)).(cpuUsage) = 37 /\
  (statistics_repaired_update {| sampleRun := 101; sampleDivisor := 1 |}
     (task_stat_set_usage statistics_initial 37)).(cpuUsage) = 0.
Proof. split; reflexivity. Qed.

Definition task_stat_statistics_rest (sg : StableGlobVars) (state : StatisticsState) : Assertion :=
  sg.(g_OSIdleCtr) # UInt |-> state.(idleCtr) **
  sg.(g_OSIdleCtrRun) # UInt |-> state.(idleCtrRun) **
  sg.(g_OSStatRdy) # UChar |-> (if state.(statReady) then 1 else 0).

Lemma task_stat_statistics_split : forall sg state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_rep sg state |--
  sg.(g_OSIdleCtrMax) # UInt |-> state.(idleCtrMax) **
  sg.(g_OSCPUUsage) # UChar |-> state.(cpuUsage) ** task_stat_statistics_rest sg state.
Proof. intros; apply statistics_rep_split_calibration_usage; assumption. Qed.

Lemma task_stat_statistics_merge_usage_store : forall sg state usage,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  sg.(g_OSIdleCtrMax) # UInt |-> state.(idleCtrMax) **
  sg.(g_OSCPUUsage) # UChar |-> usage ** task_stat_statistics_rest sg state |--
  statistics_rep sg (task_stat_set_usage state usage).
Proof.
  intros; unfold statistics_rep, task_stat_set_usage, task_stat_statistics_rest; cbn; rewrite H; entailer!.
Qed.

Lemma task_stat_statistics_merge_calibration_store : forall sg state calibration,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  sg.(g_OSIdleCtrMax) # UInt |-> calibration **
  sg.(g_OSCPUUsage) # UChar |-> state.(cpuUsage) ** task_stat_statistics_rest sg state |--
  statistics_rep sg (task_stat_set_calibration state calibration).
Proof.
  intros; unfold statistics_rep, task_stat_set_calibration, task_stat_statistics_rest; cbn; rewrite H; entailer!.
Qed.

Lemma task_stat_outside_split_statistics : forall critical sg invocation state,
  critical_region_outside critical sg invocation state |--
  statistics_rep sg state.(StatsState) ** UCOS2_raw_rep_missing_statistics sg state.
Proof.
  intros; rewrite task_stk_chk_outside_raw.
  unfold UCOS2_raw_rep_missing_statistics.
  rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule); entailer!.
Qed.

Lemma task_stat_missing_statistics_replace_eq : forall sg state statistics,
  UCOS2_raw_rep_missing_statistics sg state =
  UCOS2_raw_rep_missing_statistics sg (replace_StatsS statistics state).
Proof.
  intros; unfold UCOS2_raw_rep_missing_statistics.
  apply UCOS2_raw_rep_missing_module_frame.
  intros owner Howner; destruct owner; try reflexivity; contradiction.
Qed.

Lemma task_stat_outside_merge_statistics : forall critical sg invocation state statistics,
  statistics_rep sg statistics ** UCOS2_raw_rep_missing_statistics sg state |--
  critical_region_outside critical sg invocation (replace_StatsS statistics state).
Proof.
  intros; rewrite task_stk_chk_outside_raw.
  rewrite (task_stat_missing_statistics_replace_eq sg state statistics).
  unfold UCOS2_raw_rep_missing_statistics.
  rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule); cbn; entailer!.
Qed.

(** The next three lemmas carry arbitrary X and keep the concrete callee's
    same returned/current witnesses. The retained source predicate is a
    consequence of safeExec for that actual program, never X=True. *)
Definition task_stat_delay_observation environment critical sg caller mask ticks before
  (X : unit -> UCOS2_Verify_State -> Prop) (_ : unit) (after : UCOS2_Verify_State) : Prop :=
  time_dly_program environment critical sg caller mask ticks before tt after /\ X tt after.

Lemma task_stat_delay_safe_observation : forall environment critical sg caller mask ticks before X,
  time_dly_safe environment critical sg caller mask ticks before X ->
  time_dly_safe environment critical sg caller mask ticks before
    (task_stat_delay_observation environment critical sg caller mask ticks before X).
Proof.
  intros environment critical sg caller mask ticks before X [state [-> Hsafe]].
  exists before; split; [reflexivity|].
  intros [] after Hstep; split; [exact Hstep|apply Hsafe; exact Hstep].
Qed.

Lemma task_stat_unit_return_safe_value : forall state X,
  time_dly_return_safe state X -> X tt state.
Proof. intros state X [current [-> Hsafe]]; apply Hsafe; split; reflexivity. Qed.

Lemma task_stat_delay_post_observation : forall environment critical saved_local sg caller mask ticks before frame X,
  time_dly_call_post environment critical saved_local sg caller mask ticks before frame
    (task_stat_delay_observation environment critical sg caller mask ticks before X) |--
  EX returned current,
    coq_prop (time_dly_result environment critical sg caller mask ticks before returned current /\
      time_dly_program environment critical sg caller mask ticks before tt current /\ X tt current) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).
Proof.
  intros; unfold time_dly_call_post; Intros returned current.
  match goal with H : time_dly_result _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hresult Hsafe] end.
  pose proof (task_stat_unit_return_safe_value _ _ Hsafe) as Hsource.
  unfold task_stat_delay_observation in Hsource.
  Exists returned current; entailer!; tauto.
Qed.

Definition task_stat_suspend_observation environment critical sg caller mask request before
  (X : Z -> UCOS2_Verify_State -> Prop) (result : Z) (after : UCOS2_Verify_State) : Prop :=
  task_suspend_program environment critical sg caller mask request before result after /\ X result after.

Lemma task_stat_suspend_safe_observation : forall environment critical sg caller mask request before X,
  task_suspend_safe environment critical sg caller mask request before X ->
  task_suspend_safe environment critical sg caller mask request before
    (task_stat_suspend_observation environment critical sg caller mask request before X).
Proof.
  intros environment critical sg caller mask request before X [state [-> Hsafe]].
  exists before; split; [reflexivity|].
  intros result after Hstep; split; [exact Hstep|apply Hsafe; exact Hstep].
Qed.

Lemma task_stat_z_return_safe_value : forall (state : UCOS2_Verify_State) (result : Z)
  (X : Z -> UCOS2_Verify_State -> Prop),
  safeExec (fun current => current = state) (StateRelMonad.ret result) X -> X result state.
Proof. intros state result X [current [-> Hsafe]]; apply Hsafe; split; reflexivity. Qed.

Definition task_stat_suspend_result environment critical sg original mask before request result returned current : Prop :=
  match task_suspend_argument_error sg request with
  | Some error => result = encode_os_err_code error /\ returned = original /\ current = before
  | None => exists saved active acquired pointer priority residual released checkpoint_call checkpoint scheduled error,
      task_suspend_save_observation critical sg original active mask saved before acquired /\
      task_suspend_current_read_view sg request acquired pointer priority residual /\
      result = encode_os_err_code error /\
      task_suspend_protected sg request priority acquired (error, scheduled) released /\
      task_suspend_restore_observation critical sg active checkpoint_call released checkpoint /\
      if scheduled then task_suspend_schedule_program environment critical sg checkpoint_call mask checkpoint returned current
      else returned = checkpoint_call /\ current = checkpoint
  end.

Lemma task_stat_suspend_post_observation : forall environment critical saved_local sg original mask before request frame result X,
  task_suspend_argument_error sg request = None ->
  task_suspend_refined_call_post environment critical saved_local sg original mask before request frame result
    (task_stat_suspend_observation environment critical sg original mask request before X) |--
  EX returned current,
    coq_prop (task_stat_suspend_result environment critical sg original mask before request result returned current /\
      task_suspend_program environment critical sg original mask request before result current /\ X result current) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).
Proof.
  intros environment critical saved_local sg original mask before request frame result X Hargument.
  unfold task_suspend_refined_call_post; rewrite Hargument.
  Intros saved active acquired pointer priority residual released checkpoint_call checkpoint scheduled error.
  match goal with H : task_suspend_save_observation _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hsave [Hread [Herror [Hprotected Hrestore]]]] end.
  destruct scheduled; cbn [task_suspend_refined_tail_post].
  - unfold task_suspend_scheduler_refined_post; Intros returned current.
    match goal with H : task_suspend_schedule_program _ _ _ _ _ _ _ _ /\ _ |- _ =>
      destruct H as [Hschedule Hsafe] end.
    pose proof (task_stat_z_return_safe_value _ _ _ Hsafe) as Hsource.
    unfold task_stat_suspend_observation in Hsource.
    assert (Hresult : task_stat_suspend_result environment critical sg original mask before request result returned current).
    { unfold task_stat_suspend_result; rewrite Hargument.
      exists saved, active, acquired, pointer, priority, residual, released, checkpoint_call, checkpoint, true, error.
      exact (conj Hsave (conj Hread (conj Herror (conj Hprotected (conj Hrestore Hschedule))))). }
    Exists returned current; entailer!.
    intros heap [Hclosed Hlegacy]; exact Hclosed.
  - Intros.
    match goal with H : safeExec _ _ _ |- _ =>
      pose proof (task_stat_z_return_safe_value _ _ _ H) as Hsource end.
    unfold task_stat_suspend_observation in Hsource.
    assert (Hresult : task_stat_suspend_result environment critical sg original mask before request result checkpoint_call checkpoint).
    { unfold task_stat_suspend_result; rewrite Hargument.
      exists saved, active, acquired, pointer, priority, residual, released, checkpoint_call, checkpoint, false, error.
      exact (conj Hsave (conj Hread (conj Herror (conj Hprotected (conj Hrestore (conj eq_refl eq_refl)))))). }
    Exists checkpoint_call checkpoint; entailer!; tauto.
Qed.

(** Source control and captured C locals.  [TaskStatScaleStore] retains the
    value of the earlier unmasked load; [TaskStatUsage] retains BOTH values
    captured under the mask.  Environment intervals never replace these
    local observations with a later global value. *)
Inductive TaskStatProtectedOperation : Type :=
| TaskStatInitialize | TaskStatReset | TaskStatCapture.

Inductive TaskStatStage : Type :=
| TaskStatReady
| TaskStatReadyDelay
| TaskStatScaleLoad
| TaskStatScaleStore (loaded : Z)
| TaskStatZeroTest
| TaskStatZeroUsage
| TaskStatSelfSuspend
| TaskStatAcquire (operation : TaskStatProtectedOperation)
| TaskStatProtected (operation : TaskStatProtectedOperation) (saved : Z)
    (acquired : UCOS2_Verify_State)
| TaskStatRelease (operation : TaskStatProtectedOperation) (saved : Z)
    (acquired : UCOS2_Verify_State) (sample : StatisticsSample)
| TaskStatOneTick
| TaskStatSampleWindow
| TaskStatUsage (sample : StatisticsSample)
| TaskStatRecalibrate (sample : StatisticsSample)
| TaskStatHook
| TaskStatStack.

Record TaskStatPoint : Type := {
  task_stat_stage : TaskStatStage;
  task_stat_caller : TaskSuspendCaller;
  task_stat_mask : Z
}.

Definition task_stat_at stage caller mask : TaskStatPoint :=
  {| task_stat_stage := stage; task_stat_caller := caller; task_stat_mask := mask |}.

Definition task_stat_unmasked (stage : TaskStatStage) : bool :=
  match stage with TaskStatProtected _ _ _ | TaskStatRelease _ _ _ _ => false | _ => true end.

Definition task_stat_protected_statistics operation (state : StatisticsState) : StatisticsState :=
  match operation with
  | TaskStatInitialize => task_stat_initial_counter state
  | TaskStatReset => statistics_reset_counter state
  | TaskStatCapture => snd (statistics_capture state)
  end.

Definition task_stat_protected_sample operation (state : StatisticsState) : StatisticsSample :=
  match operation with
  | TaskStatCapture => fst (statistics_capture state)
  | _ => {| sampleRun := 0; sampleDivisor := 0 |}
  end.

Definition task_stat_after_release operation sample : TaskStatStage :=
  match operation with
  | TaskStatInitialize => TaskStatOneTick
  | TaskStatReset => TaskStatSampleWindow
  | TaskStatCapture => TaskStatUsage sample
  end.

Definition task_stat_after_usage sample : TaskStatStage :=
  if task_stat_needs_recalibration sample then TaskStatRecalibrate sample else TaskStatHook.

Definition task_stat_store_instruction (stage : TaskStatStage)
  : option (StatisticsStoreField * Z * TaskStatStage) :=
  match stage with
  | TaskStatScaleStore loaded => Some (StatisticsCalibrationField, loaded / 100, TaskStatZeroTest)
  | TaskStatZeroUsage => Some (StatisticsUsageField, 0, TaskStatSelfSuspend)
  | TaskStatUsage sample => Some (StatisticsUsageField, task_stat_sample_usage sample,
      task_stat_after_usage sample)
  | TaskStatRecalibrate sample => Some (StatisticsCalibrationField, sample.(sampleRun) / 100, TaskStatHook)
  | _ => None
  end.

Definition task_stat_delay_instruction (stage : TaskStatStage) : option (Z * TaskStatStage) :=
  match stage with
  | TaskStatReadyDelay => Some (20, TaskStatReady)
  | TaskStatOneTick => Some (1, TaskStatAcquire TaskStatReset)
  | TaskStatSampleWindow => Some (10, TaskStatAcquire TaskStatCapture)
  | _ => None
  end.

(** The exact existing Suspend entry requirements, specialised to the real
    self argument.  They are call admissions, never consequences of closed
    kernel ownership. *)
Definition task_stat_suspend_admission (environment : TaskStackCallEnvironment) critical sg caller mask before : Prop :=
  valid_stable_glob_vars sg /\ sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(g_OSTCBTbl) mod 4 = 0 /\
  task_suspend_completed_calls critical sg caller sg.(osPrioSelf) mask before /\
  task_suspend_scheduler_clients critical caller.

Definition task_stat_call_admission environment critical saved_local sg frame
  (point : TaskStatPoint) state : Prop :=
  match task_stat_delay_instruction point.(task_stat_stage) with
  | Some (ticks, _) => time_dly_entry_facts environment critical sg point.(task_stat_caller)
      point.(task_stat_mask) ticks state
  | None => match point.(task_stat_stage) with
      | TaskStatSelfSuspend => task_stat_suspend_admission environment critical sg
          point.(task_stat_caller) point.(task_stat_mask) state
      | TaskStatStack => task_stat_stk_chk_continuation_protocol environment critical saved_local sg
          point.(task_stat_caller) point.(task_stat_mask) frame state
      | _ => True
      end
  end.

(** Each constructor is one real source cut.  Call steps carry the actual
    returned caller, not the original caller.  Interference is an explicit
    resumption interval at an unmasked cut; it leaves C locals unchanged.
    The relation does not manufacture a concrete endpoint heap.  The
    resource adapter below takes the actual endpoint on that SAME heap. *)
Inductive task_stat_step environment critical saved_local sg (frame : Assertion)
  : TaskStatPoint -> UCOS2_Verify_State -> TaskStatPoint -> UCOS2_Verify_State -> Prop :=
| task_stat_step_interference : forall stage caller returned mask before after,
    task_stat_unmasked stage = true ->
    critical_region_interval critical sg
      (task_suspend_view caller).(os_execution_invocation) before after ->
    task_suspend_same_call returned caller ->
    task_stat_step environment critical saved_local sg frame
      (task_stat_at stage caller mask) before (task_stat_at stage returned mask) after
| task_stat_step_ready : forall caller mask state,
    task_stat_step environment critical saved_local sg frame
      (task_stat_at TaskStatReady caller mask) state
      (task_stat_at (if state.(StatsState).(statReady) then TaskStatScaleLoad
        else TaskStatReadyDelay) caller mask) state
| task_stat_step_scale_load : forall caller mask state,
    task_stat_step environment critical saved_local sg frame
      (task_stat_at TaskStatScaleLoad caller mask) state
      (task_stat_at (TaskStatScaleStore state.(StatsState).(idleCtrMax)) caller mask) state
| task_stat_step_zero_test : forall caller mask state,
    task_stat_step environment critical saved_local sg frame
      (task_stat_at TaskStatZeroTest caller mask) state
      (task_stat_at (if Z.eqb state.(StatsState).(idleCtrMax) 0 then TaskStatZeroUsage
        else TaskStatAcquire TaskStatInitialize) caller mask) state
| task_stat_step_store : forall stage field stored next caller mask state,
    task_stat_store_instruction stage = Some (field, stored, next) ->
    task_stat_step environment critical saved_local sg frame
      (task_stat_at stage caller mask) state (task_stat_at next caller mask)
      (replace_StatsS (statistics_store_state field stored state.(StatsState)) state)
| task_stat_step_delay : forall stage ticks next caller returned mask before after,
    task_stat_delay_instruction stage = Some (ticks, next) ->
    time_dly_program environment critical sg caller mask ticks before tt after ->
    time_dly_result environment critical sg caller mask ticks before returned after ->
    task_stat_step environment critical saved_local sg frame
      (task_stat_at stage caller mask) before (task_stat_at next returned mask) after
| task_stat_step_suspend : forall caller returned mask before result after,
    task_suspend_program environment critical sg caller mask sg.(osPrioSelf) before result after ->
    task_stat_suspend_result environment critical sg caller mask before sg.(osPrioSelf)
      result returned after ->
    task_stat_step environment critical saved_local sg frame
      (task_stat_at TaskStatSelfSuspend caller mask) before
      (task_stat_at TaskStatZeroTest returned mask) after
| task_stat_step_save : forall operation caller returned mask saved before acquired,
    task_suspend_save_observation critical sg caller returned mask saved before acquired ->
    task_suspend_save_effect environment critical sg caller returned mask saved before acquired ->
    task_stat_step environment critical saved_local sg frame
      (task_stat_at (TaskStatAcquire operation) caller mask) before
      (task_stat_at (TaskStatProtected operation saved acquired) returned mask) acquired
| task_stat_step_protected : forall operation caller mask saved acquired state,
    task_stat_step environment critical saved_local sg frame
      (task_stat_at (TaskStatProtected operation saved acquired) caller mask) state
      (task_stat_at (TaskStatRelease operation saved acquired
        (task_stat_protected_sample operation state.(StatsState))) caller mask)
      (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state)
| task_stat_step_restore : forall operation sample caller returned mask saved acquired released current,
    task_suspend_restore_observation critical sg caller returned released current ->
    task_suspend_restore_effect environment critical sg caller returned released current ->
    task_stat_step environment critical saved_local sg frame
      (task_stat_at (TaskStatRelease operation saved acquired sample) caller mask) released
      (task_stat_at (task_stat_after_release operation sample) returned (armv7a_irq_fiq_mask saved)) current
| task_stat_step_hook : forall caller mask state,
    task_stat_step environment critical saved_local sg frame
      (task_stat_at TaskStatHook caller mask) state (task_stat_at TaskStatStack caller mask) state
| task_stat_step_stack : forall caller returned mask before after,
    task_stat_stk_chk_continuation_program environment critical saved_local sg caller mask frame
      before returned after ->
    task_stat_step environment critical saved_local sg frame
      (task_stat_at TaskStatStack caller mask) before (task_stat_at TaskStatOneTick returned mask) after.

Inductive task_stat_prefix environment critical saved_local sg frame point state
  : TaskStatPoint -> UCOS2_Verify_State -> Prop :=
| task_stat_prefix_refl : task_stat_prefix environment critical saved_local sg frame point state point state
| task_stat_prefix_snoc : forall middle current next after,
    task_stat_prefix environment critical saved_local sg frame point state middle current ->
    task_stat_step environment critical saved_local sg frame middle current next after ->
    task_stat_prefix environment critical saved_local sg frame point state next after.

Definition task_stat_program environment critical saved_local sg frame point
  : program UCOS2_Verify_State TaskStatPoint :=
  fun before next after => task_stat_prefix environment critical saved_local sg frame point before next after.

(** A conditional safety specification for EVERY reached finite prefix.
    It requires only existing callee admissions at actual reachable cuts.
    There is no premise asserting a future return, positive calibration,
    readable stack scan, or scheduling progress. *)
Definition task_stat_protocol environment critical saved_local sg frame point before : Prop :=
  forall next after, task_stat_prefix environment critical saved_local sg frame point before next after ->
    task_stat_call_admission environment critical saved_local sg frame next after.

Definition task_stat_context environment critical saved_local sg frame point before
  (X : TaskStatPoint -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun current => current = before)
    (task_stat_program environment critical saved_local sg frame point) X /\
  task_stat_protocol environment critical saved_local sg frame point before.

Lemma task_stat_prefix_trans : forall environment critical saved_local sg frame point before middle current next after,
  task_stat_prefix environment critical saved_local sg frame point before middle current ->
  task_stat_prefix environment critical saved_local sg frame middle current next after ->
  task_stat_prefix environment critical saved_local sg frame point before next after.
Proof.
  intros * Hprefix Htail; induction Htail.
  - exact Hprefix.
  - eapply task_stat_prefix_snoc; eassumption.
Qed.

Lemma task_stat_context_current : forall environment critical saved_local sg frame point before X,
  task_stat_context environment critical saved_local sg frame point before X ->
  X point before /\ task_stat_call_admission environment critical saved_local sg frame point before.
Proof.
  intros * [[state [-> Hsafe]] Hprotocol].
  split; [apply Hsafe|apply Hprotocol]; constructor.
Qed.

Lemma task_stat_context_step : forall environment critical saved_local sg frame point before next after X,
  task_stat_context environment critical saved_local sg frame point before X ->
  task_stat_step environment critical saved_local sg frame point before next after ->
  task_stat_context environment critical saved_local sg frame next after X.
Proof.
  intros * [[state [-> Hsafe]] Hprotocol] Hstep.
  assert (Hprefix : task_stat_prefix environment critical saved_local sg frame point before next after).
  { eapply task_stat_prefix_snoc; [constructor|exact Hstep]. }
  split.
  - exists after; split; [reflexivity|].
    intros endpoint final Htail; apply Hsafe.
    eapply task_stat_prefix_trans; eassumption.
  - intros endpoint final Htail; apply Hprotocol.
    eapply task_stat_prefix_trans; eassumption.
Qed.

Definition task_stat_delay_continuation environment critical saved_local sg frame (stage : TaskStatStage) caller mask
  ticks next before (X : TaskStatPoint -> UCOS2_Verify_State -> Prop) (_ : unit) after : Prop :=
  forall returned,
    time_dly_result environment critical sg caller mask ticks before returned after ->
    task_stat_context environment critical saved_local sg frame (task_stat_at next returned mask) after X.

Lemma task_stat_context_delay_safe : forall environment critical saved_local sg frame stage caller mask
  ticks next before X,
  task_stat_delay_instruction stage = Some (ticks, next) ->
  task_stat_context environment critical saved_local sg frame (task_stat_at stage caller mask) before X ->
  time_dly_safe environment critical sg caller mask ticks before
    (task_stat_delay_continuation environment critical saved_local sg frame stage caller mask ticks next before X).
Proof.
  intros * Hinstruction Hcontext; exists before; split; [reflexivity|].
  intros [] after Hprogram returned Hresult.
  eapply task_stat_context_step; [exact Hcontext|].
  eapply task_stat_step_delay; eassumption.
Qed.

Lemma task_stat_delay_post_context : forall environment critical saved_local sg frame stage caller mask
  ticks next before X,
  time_dly_call_post environment critical saved_local sg caller mask ticks before frame
    (task_stat_delay_continuation environment critical saved_local sg frame stage caller mask ticks next before X) |--
  EX returned current,
    coq_prop (task_stat_context environment critical saved_local sg frame
      (task_stat_at next returned mask) current X) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).
Proof.
  intros; unfold time_dly_call_post; Intros returned current.
  match goal with H : time_dly_result _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hresult Hsafe] end.
  pose proof (task_stat_unit_return_safe_value _ _ Hsafe) as Hcontinuation.
  Exists returned current; entailer!; apply Hcontinuation; exact Hresult.
Qed.

Definition task_stat_suspend_continuation environment critical saved_local sg frame caller mask before
  (X : TaskStatPoint -> UCOS2_Verify_State -> Prop) result after : Prop :=
  forall returned,
    task_stat_suspend_result environment critical sg caller mask before sg.(osPrioSelf) result returned after ->
    task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatZeroTest returned mask) after X.

Lemma task_stat_context_suspend_safe : forall environment critical saved_local sg frame caller mask before X,
  task_stat_context environment critical saved_local sg frame
    (task_stat_at TaskStatSelfSuspend caller mask) before X ->
  task_suspend_safe environment critical sg caller mask sg.(osPrioSelf) before
    (task_stat_suspend_continuation environment critical saved_local sg frame caller mask before X).
Proof.
  intros * Hcontext; exists before; split; [reflexivity|].
  intros result after Hprogram returned Hresult.
  eapply task_stat_context_step; [exact Hcontext|].
  eapply task_stat_step_suspend; eassumption.
Qed.

Lemma task_stat_suspend_post_context : forall environment critical saved_local sg frame caller mask before result X,
  task_suspend_argument_error sg sg.(osPrioSelf) = None ->
  task_suspend_refined_call_post environment critical saved_local sg caller mask before sg.(osPrioSelf) frame result
    (task_stat_suspend_observation environment critical sg caller mask sg.(osPrioSelf) before
      (task_stat_suspend_continuation environment critical saved_local sg frame caller mask before X)) |--
  EX returned current,
    coq_prop (task_stat_context environment critical saved_local sg frame
      (task_stat_at TaskStatZeroTest returned mask) current X) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).
Proof.
  intros * Hargument.
  sep_apply_l_atomic (task_stat_suspend_post_observation environment critical saved_local sg caller mask before
    sg.(osPrioSelf) frame result
    (task_stat_suspend_continuation environment critical saved_local sg frame caller mask before X) Hargument).
  Intros returned current.
  match goal with H : task_stat_suspend_result _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hresult [Hprogram Hcontinuation]] end.
  Exists returned current; entailer!; apply Hcontinuation; exact Hresult.
Qed.

Definition task_stat_stack_continuation environment critical saved_local sg frame caller mask before
  (X : TaskStatPoint -> UCOS2_Verify_State -> Prop) (_ : unit) after : Prop :=
  forall returned,
    task_stat_stk_chk_continuation_program environment critical saved_local sg caller mask frame before returned after ->
    task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatOneTick returned mask) after X.

Lemma task_stat_context_stack_safe : forall environment critical saved_local sg frame caller mask before X,
  task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatStack caller mask) before X ->
  task_stat_stk_chk_continuation_safe environment critical saved_local sg caller mask frame before
    (task_stat_stack_continuation environment critical saved_local sg frame caller mask before X).
Proof.
  intros * Hcontext; exists before; split; [reflexivity|].
  intros ignored after Hprogram returned Hreturned.
  eapply task_stat_context_step; [exact Hcontext|].
  apply task_stat_step_stack; exact Hreturned.
Qed.

Lemma task_stat_stack_post_context : forall environment critical saved_local sg frame caller mask before X,
  task_stat_stk_chk_continuation_post environment critical saved_local sg caller mask frame before
    (task_stat_stack_continuation environment critical saved_local sg frame caller mask before X) |--
  EX returned current,
    coq_prop (task_stat_context environment critical saved_local sg frame
      (task_stat_at TaskStatOneTick returned mask) current X) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).
Proof.
  intros; unfold task_stat_stk_chk_continuation_post; Intros output history returned current.
  match goal with H : _ <> 0 /\ task_stat_stk_chk_continuation_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Houtput [Hprefix Hcontinuation]] end.
  assert (Hsource : task_stat_stk_chk_continuation_program environment critical saved_local sg caller mask frame
    before returned current).
  { exists output, history; auto. }
  Exists returned current; entailer!; apply Hcontinuation; exact Hsource.
Qed.

(** Caller-private resources depend on the Task projection, not statistics.
    This is an equality of the SAME residual heap, not an environment step. *)
Lemma task_stat_call_resources_replace_statistics : forall environment saved_local sg caller state statistics,
  task_suspend_call_resources environment saved_local sg caller (replace_StatsS statistics state) =
  task_suspend_call_resources environment saved_local sg caller state.
Proof.
  intros; destruct caller; unfold task_suspend_call_resources,
    task_tcb_init_continuation_capsules; reflexivity.
Qed.

Lemma task_stat_outside_resources_replace_statistics : forall environment saved_local sg caller mask state statistics,
  time_dly_outside_resources environment saved_local sg caller mask (replace_StatsS statistics state) =
  time_dly_outside_resources environment saved_local sg caller mask state.
Proof.
  intros; unfold time_dly_outside_resources; rewrite task_stat_call_resources_replace_statistics; reflexivity.
Qed.

Definition task_stat_closed_statistics_frame environment saved_local sg caller mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
  (UCOS2_raw_rep_missing_module sg state StatisticsModule **
   time_dly_outside_resources environment saved_local sg caller mask state).

Lemma task_stat_closed_split_statistics : forall environment critical saved_local sg caller mask state,
  task_suspend_closed environment critical saved_local sg caller mask state --||--
  (statistics_rep sg state.(StatsState) **
    task_stat_closed_statistics_frame environment saved_local sg caller mask state).
Proof.
  intros; rewrite time_dly_closed_inv_equiv; unfold UCOS2_inv, task_stat_closed_statistics_frame.
  rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule); cbn [UCOS2_module_rep]; split; entailer!.
Qed.

Lemma task_stat_closed_merge_statistics : forall environment critical saved_local sg caller mask state statistics,
  UCOS2_state_inv sg (replace_StatsS statistics state) ->
  statistics_rep sg statistics ** task_stat_closed_statistics_frame environment saved_local sg caller mask state |--
  task_suspend_closed environment critical saved_local sg caller mask (replace_StatsS statistics state).
Proof.
  intros * Hvalid; rewrite time_dly_closed_inv_equiv.
  unfold task_stat_closed_statistics_frame; Intros.
  rewrite task_stat_outside_resources_replace_statistics.
  pose proof (UCOS2_inv_merge_updated_module sg state
    (replace_StatsS statistics state) StatisticsModule Hvalid ltac:(reflexivity)) as Hmerge.
  change (statistics_rep sg statistics ** UCOS2_raw_rep_missing_module sg state StatisticsModule |--
    UCOS2_inv sg (replace_StatsS statistics state)) in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma task_stat_closed_load : forall environment critical saved_local sg caller mask state frame field heap,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (task_suspend_closed environment critical saved_local sg caller mask state ** frame) heap ->
  statistics_load_fragment sg field (statistics_load_value field state.(StatsState)) heap.
Proof.
  intros * Henabled Hheap.
  assert (Hraw : task_suspend_closed environment critical saved_local sg caller mask state ** frame |--
    UCOS2_raw_rep sg state **
      (time_dly_outside_resources environment saved_local sg caller mask state ** frame)).
  { rewrite time_dly_closed_inv_equiv; unfold UCOS2_inv; entailer!. }
  eapply statistics_load_resources; [exact Henabled|apply Hraw; exact Hheap].
Qed.

Lemma task_stat_closed_store_resources : forall environment critical saved_local sg caller mask state frame
  field stored before after,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (task_suspend_closed environment critical saved_local sg caller mask state ** frame) before ->
  statistics_store_fragment sg field stored before after ->
  (task_suspend_closed environment critical saved_local sg caller mask
    (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame) after.
Proof.
  intros * Henabled Hbefore Hrun.
  assert (Hsplit : task_suspend_closed environment critical saved_local sg caller mask state ** frame |--
    UCOS2_inv sg state ** (time_dly_outside_resources environment saved_local sg caller mask state ** frame)).
  { rewrite time_dly_closed_inv_equiv; entailer!. }
  pose proof (statistics_store_resources sg field stored state _ before after Henabled (Hsplit _ Hbefore) Hrun) as Hafter.
  assert (Hmerge : UCOS2_inv sg (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) **
      (time_dly_outside_resources environment saved_local sg caller mask state ** frame) |--
    task_suspend_closed environment critical saved_local sg caller mask
      (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame).
  { rewrite time_dly_closed_inv_equiv, task_stat_outside_resources_replace_statistics; entailer!. }
  exact (Hmerge _ Hafter).
Qed.

(** Actual source execution implies both continuation and ownership at its
    supplied endpoint.  No existentially produced replacement heap is used. *)
Lemma task_stat_store_step_resources : forall environment critical saved_local sg frame stage caller mask state X
  field stored next before after,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_stat_context environment critical saved_local sg frame (task_stat_at stage caller mask) state X ->
  task_stat_store_instruction stage = Some (field, stored, next) ->
  (task_suspend_closed environment critical saved_local sg caller mask state ** frame) before ->
  statistics_store_fragment sg field stored before after ->
  let current := replace_StatsS (statistics_store_state field stored state.(StatsState)) state in
  task_stat_context environment critical saved_local sg frame (task_stat_at next caller mask) current X /\
  (task_suspend_closed environment critical saved_local sg caller mask current ** frame) after.
Proof.
  intros * Henabled Hcontext Hinstruction Hbefore Hrun current; split.
  - eapply task_stat_context_step; [exact Hcontext|].
    apply task_stat_step_store; exact Hinstruction.
  - eapply task_stat_closed_store_resources; eassumption.
Qed.

Lemma task_stat_interference_return_resources : forall environment critical saved_local sg frame stage caller returned
  mask before after X endpoint,
  task_stat_unmasked stage = true ->
  task_stat_context environment critical saved_local sg frame (task_stat_at stage caller mask) before X ->
  critical_region_interval critical sg
    (task_suspend_view caller).(os_execution_invocation) before after ->
  task_suspend_same_call returned caller ->
  (task_suspend_closed environment critical saved_local sg returned mask after ** frame) endpoint ->
  task_stat_context environment critical saved_local sg frame (task_stat_at stage returned mask) after X /\
  (task_suspend_closed environment critical saved_local sg returned mask after ** frame) endpoint.
Proof.
  intros * Hunmasked Hcontext Hinterval Hsame Hendpoint; split; [|exact Hendpoint].
  eapply task_stat_context_step; [exact Hcontext|].
  apply task_stat_step_interference; assumption.
Qed.

Definition task_stat_protected_address sg operation : Z :=
  match operation with TaskStatCapture => sg.(g_OSIdleCtrRun) | _ => sg.(g_OSIdleCtr) end.
Definition task_stat_protected_old operation (state : StatisticsState) : Z :=
  match operation with TaskStatCapture => state.(idleCtrRun) | _ => state.(idleCtr) end.
Definition task_stat_protected_value operation (state : StatisticsState) : Z :=
  match operation with
  | TaskStatInitialize => kernel_u32 (state.(idleCtrMax) * 100)
  | TaskStatReset => 0
  | TaskStatCapture => state.(idleCtr)
  end.
Definition task_stat_protected_residual sg operation (state : StatisticsState) : Assertion :=
  sg.(g_OSIdleCtrMax) # UInt |-> state.(idleCtrMax) **
  sg.(g_OSCPUUsage) # UChar |-> state.(cpuUsage) **
  sg.(g_OSStatRdy) # UChar |-> (if state.(statReady) then 1 else 0) **
  match operation with
  | TaskStatCapture => sg.(g_OSIdleCtr) # UInt |-> state.(idleCtr)
  | _ => sg.(g_OSIdleCtrRun) # UInt |-> state.(idleCtrRun)
  end.

Lemma task_stat_protected_split : forall sg operation state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_rep sg state |--
    task_stat_protected_address sg operation # UInt |-> task_stat_protected_old operation state **
    task_stat_protected_residual sg operation state.
Proof.
  intros; destruct operation; unfold statistics_rep, task_stat_protected_address,
    task_stat_protected_old, task_stat_protected_residual; rewrite H; entailer!.
Qed.

Lemma task_stat_protected_merge : forall sg operation state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_stat_protected_address sg operation # UInt |-> task_stat_protected_value operation state **
    task_stat_protected_residual sg operation state |--
  statistics_rep sg (task_stat_protected_statistics operation state).
Proof.
  intros; destruct operation; unfold statistics_rep, task_stat_protected_address,
    task_stat_protected_value, task_stat_protected_residual, task_stat_protected_statistics,
    task_stat_initial_counter, statistics_set_counter, statistics_reset_counter, statistics_capture;
    cbn; rewrite H; entailer!.
Qed.

Lemma task_stat_protected_valid : forall sg operation state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true -> UCOS2_state_inv sg state ->
  UCOS2_state_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state).
Proof.
  intros * Henabled Hvalid; apply statistics_replace_preserves_validity; [exact Hvalid|].
  apply statistics_enabled_update_preserves_configuration with
    (update := task_stat_protected_statistics operation); [exact Henabled| |].
  - intros statistics Hstatistics; destruct operation; cbn [task_stat_protected_statistics].
    + apply task_stat_initial_counter_preserves_validity; exact Hstatistics.
    + apply statistics_reset_counter_preserves_validity; exact Hstatistics.
    + exact (proj2 (statistics_capture_preserves_validity statistics Hstatistics)).
  - unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
Qed.

Lemma task_stat_protected_value_in_range : forall operation state,
  valid_statistics_state state -> 0 <= task_stat_protected_value operation state < 4294967296.
Proof.
  intros operation state Hvalid; destruct operation; cbn [task_stat_protected_value].
  - apply kernel_u32_in_range.
  - lia.
  - unfold valid_statistics_state in Hvalid; tauto.
Qed.

Lemma task_stat_protected_produces : forall sg operation state (frame : Assertion) before,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_inv sg state ** frame) before ->
  exists after,
    kernel_heap_execution (KernelHeapStorage.pointer_store_writes (task_stat_protected_address sg operation)
      (task_stat_protected_value operation state.(StatsState))) before after /\
    (UCOS2_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state) ** frame) after.
Proof.
  intros * Henabled Hbefore.
  assert (Hsplit : UCOS2_inv sg state ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (task_stat_protected_address sg operation # UInt |-> task_stat_protected_old operation state.(StatsState) **
      (task_stat_protected_residual sg operation state.(StatsState) **
       UCOS2_raw_rep_missing_module sg state StatisticsModule ** frame))).
  { unfold UCOS2_inv; Intros; rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule).
    cbn [UCOS2_module_rep]; sep_apply_l_atomic (task_stat_protected_split sg operation state.(StatsState) Henabled);
      entailer!. }
  destruct (Hsplit _ Hbefore) as [Hvalid Hcells].
  change (UCOS2_state_inv sg state) in Hvalid.
  assert (Hrange : 0 <= task_stat_protected_value operation state.(StatsState) < 4294967296).
  { apply task_stat_protected_value_in_range.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_statistics_configuration in Hvalid; tauto. }
  destruct (statistics_framed_uint_store _ _ _ _ before Hrange Hcells) as [after [Hrun Hafter]].
  assert (Hpost : UCOS2_state_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state))
    by (apply task_stat_protected_valid; assumption).
  assert (Hmerge : task_stat_protected_address sg operation # UInt |-> task_stat_protected_value operation state.(StatsState) **
      (task_stat_protected_residual sg operation state.(StatsState) **
       UCOS2_raw_rep_missing_module sg state StatisticsModule ** frame) |--
    UCOS2_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state) ** frame).
  { sep_apply_l_atomic (task_stat_protected_merge sg operation state.(StatsState) Henabled).
    pose proof (UCOS2_inv_merge_updated_module sg state
      (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state)
      StatisticsModule Hpost ltac:(reflexivity)) as Hmodule.
    change (statistics_rep sg (task_stat_protected_statistics operation state.(StatsState)) **
      UCOS2_raw_rep_missing_module sg state StatisticsModule |--
      UCOS2_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state)) in Hmodule.
    sep_apply_l_atomic Hmodule; entailer!. }
  exists after; split; [exact Hrun|apply Hmerge; exact Hafter].
Qed.

Lemma task_stat_protected_store_resources : forall sg operation state (frame : Assertion) before after,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_inv sg state ** frame) before ->
  kernel_heap_execution (KernelHeapStorage.pointer_store_writes (task_stat_protected_address sg operation)
    (task_stat_protected_value operation state.(StatsState))) before after ->
  (UCOS2_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state) ** frame) after.
Proof.
  intros * Henabled Hbefore Hrun.
  destruct (task_stat_protected_produces sg operation state frame before Henabled Hbefore)
    as [produced [Hproduced Hafter]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hafter.
Qed.

(** Masked source order: initialization reads Max before its counter store;
    capture reads Counter, writes Run, then reads Run and Max.  They are not
    observations of a later Restore state. *)
Definition task_stat_protected_fragment sg operation state sample (before after : model) : Prop :=
  match operation with
  | TaskStatInitialize =>
      KernelHeapObservation.pointer_load sg.(g_OSIdleCtrMax) state.(idleCtrMax) before /\
      kernel_heap_execution (KernelHeapStorage.pointer_store_writes sg.(g_OSIdleCtr)
        (kernel_u32 (state.(idleCtrMax) * 100))) before after /\
      sample = {| sampleRun := 0; sampleDivisor := 0 |}
  | TaskStatReset =>
      kernel_heap_execution (KernelHeapStorage.pointer_store_writes sg.(g_OSIdleCtr) 0) before after /\
      sample = {| sampleRun := 0; sampleDivisor := 0 |}
  | TaskStatCapture =>
      KernelHeapObservation.pointer_load sg.(g_OSIdleCtr) state.(idleCtr) before /\
      kernel_heap_execution (KernelHeapStorage.pointer_store_writes sg.(g_OSIdleCtrRun) state.(idleCtr)) before after /\
      KernelHeapObservation.pointer_load sg.(g_OSIdleCtrRun) sample.(sampleRun) after /\
      KernelHeapObservation.pointer_load sg.(g_OSIdleCtrMax) sample.(sampleDivisor) after
  end.

Lemma task_stat_inv_uint_load : forall sg state frame heap address value,
  (UCOS2_inv sg state ** frame) heap ->
  (UCOS2_inv sg state ** frame |-- address # UInt |-> value ** TT) ->
  KernelHeapObservation.pointer_load address value heap.
Proof.
  intros * Hheap Hfocus; apply KernelHeapObservation.framed_pointer_store_load with (frame := TT).
  assert (Hcast : (address # UInt |-> value ** TT) |-- (address # Ptr |-> value ** TT)).
  { rewrite statistics_uint_pointer_rep; entailer!. }
  apply Hcast; apply Hfocus; exact Hheap.
Qed.

Lemma task_stat_protected_fragment_produces : forall sg operation state (frame : Assertion) before,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_inv sg state ** frame) before ->
  exists after,
    task_stat_protected_fragment sg operation state.(StatsState)
      (task_stat_protected_sample operation state.(StatsState)) before after /\
    (UCOS2_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state) ** frame) after.
Proof.
  intros * Henabled Hbefore.
  destruct (task_stat_protected_produces sg operation state frame before Henabled Hbefore)
    as [after [Hrun Hafter]].
  exists after; split; [|exact Hafter].
  assert (Hmax : KernelHeapObservation.pointer_load sg.(g_OSIdleCtrMax) state.(StatsState).(idleCtrMax) before).
  { eapply task_stat_inv_uint_load; [exact Hbefore|].
    unfold UCOS2_inv; rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule);
      cbn [UCOS2_module_rep]; unfold statistics_rep; rewrite Henabled; cbn [task_stat_protected_statistics replace_StatsS statistics_capture StatsState idleCtr idleCtrRun idleCtrMax cpuUsage statReady sampleRun sampleDivisor fst snd]; entailer!; intros ? ?; exact I. }
  destruct operation; cbn [task_stat_protected_fragment task_stat_protected_sample statistics_capture] in *.
  - split; [exact Hmax|]; split; [exact Hrun|reflexivity].
  - split; [exact Hrun|reflexivity].
  - split.
    + eapply task_stat_inv_uint_load; [exact Hbefore|].
      unfold UCOS2_inv; rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule);
        cbn [UCOS2_module_rep]; unfold statistics_rep; rewrite Henabled; cbn [task_stat_protected_statistics replace_StatsS statistics_capture StatsState idleCtr idleCtrRun idleCtrMax cpuUsage statReady sampleRun sampleDivisor fst snd]; entailer!; intros ? ?; exact I.
    + split; [exact Hrun|]; split;
        eapply task_stat_inv_uint_load; try exact Hafter;
        unfold UCOS2_inv; rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule);
        cbn [UCOS2_module_rep replace_StatsS task_stat_protected_statistics statistics_capture];
        unfold statistics_rep; rewrite Henabled; cbn [task_stat_protected_statistics replace_StatsS statistics_capture StatsState idleCtr idleCtrRun idleCtrMax cpuUsage statReady sampleRun sampleDivisor fst snd]; entailer!; intros ? ?; exact I.
Qed.

Lemma task_stat_protected_fragment_resources : forall sg operation state (frame : Assertion) before after sample,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_inv sg state ** frame) before ->
  task_stat_protected_fragment sg operation state.(StatsState) sample before after ->
  sample = task_stat_protected_sample operation state.(StatsState) /\
  (UCOS2_inv sg (replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state) ** frame) after.
Proof.
  intros * Henabled Hbefore Hfragment.
  destruct (task_stat_protected_fragment_produces sg operation state frame before Henabled Hbefore)
    as [produced [Hproduced Hresources]].
  destruct operation; cbn [task_stat_protected_fragment task_stat_protected_sample statistics_capture] in *.
  - destruct Hfragment as [Hload [Hrun Hsample]], Hproduced as [Hexpected [Hrun' Hsample']].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
    subst produced; auto.
  - destruct Hfragment as [Hrun Hsample], Hproduced as [Hrun' Hsample'].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
    subst produced; auto.
  - destruct Hfragment as [Hload [Hrun [Hrunload Hmaxload]]],
      Hproduced as [Hexpected [Hrun' [Hrunload' Hmaxload']]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
    subst produced; split; [|exact Hresources].
    assert (Hrunvalue : sampleRun sample = idleCtr (StatsState state))
      by (eapply KernelHeapObservation.pointer_load_deterministic; eassumption).
    assert (Hmaxvalue : sampleDivisor sample = idleCtrMax (StatsState state))
      by (eapply KernelHeapObservation.pointer_load_deterministic; eassumption).
    destruct sample; cbn in *; subst; reflexivity.
Qed.

Definition task_stat_configuration (sg : StableGlobVars) : Prop :=
  valid_stable_glob_vars sg /\ sg.(osKernelConfig).(cfgStatisticsEnabled) = true /\
  task_stat_stk_chk_configuration sg.

Definition task_stat_statistics_addresses (sg : StableGlobVars) ctr maximum run usage ready : Prop :=
  sg.(g_OSIdleCtr) = ctr /\ sg.(g_OSIdleCtrMax) = maximum /\
  sg.(g_OSIdleCtrRun) = run /\ sg.(g_OSCPUUsage) = usage /\ sg.(g_OSStatRdy) = ready.

Definition task_stat_counter (state : UCOS2_Verify_State) : Z := state.(StatsState).(idleCtr).
Definition task_stat_maximum (state : UCOS2_Verify_State) : Z := state.(StatsState).(idleCtrMax).
Definition task_stat_run (state : UCOS2_Verify_State) : Z := state.(StatsState).(idleCtrRun).
Definition task_stat_usage (state : UCOS2_Verify_State) : Z := state.(StatsState).(cpuUsage).
Definition task_stat_ready (state : UCOS2_Verify_State) : Z := if state.(StatsState).(statReady) then 1 else 0.
Definition task_stat_sample run maximum : StatisticsSample := {| sampleRun := run; sampleDivisor := maximum |}.

Definition task_stat_closed_checkpoint environment critical saved_local sg frame stage caller mask state X : Assertion :=
  coq_prop (task_stat_context environment critical saved_local sg frame (task_stat_at stage caller mask) state X) &&
  (task_suspend_closed environment critical saved_local sg caller mask state ** frame).

Definition task_stat_masked_checkpoint environment critical saved_local sg frame stage caller mask saved acquired state X : Assertion :=
  coq_prop (task_stat_context environment critical saved_local sg frame (task_stat_at stage caller mask) state X) &&
  (task_suspend_masked environment critical saved_local sg caller saved acquired state ** frame).

Definition task_stat_masked_statistics_frame environment critical saved_local sg caller saved acquired state : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
  (UCOS2_raw_rep_missing_module sg state StatisticsModule **
   critical_region_masked environment.(task_stack_call_platform) critical sg
     (task_suspend_view caller).(os_execution_invocation) (task_suspend_view caller).(os_execution_origin) saved acquired **
   task_suspend_call_resources environment saved_local sg caller state).

Lemma task_stat_masked_split_statistics : forall environment critical saved_local sg caller saved acquired state,
  task_suspend_masked environment critical saved_local sg caller saved acquired state --||--
  (statistics_rep sg state.(StatsState) **
    task_stat_masked_statistics_frame environment critical saved_local sg caller saved acquired state).
Proof.
  intros; unfold task_suspend_masked, task_stat_masked_statistics_frame, UCOS2_inv.
  rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule); cbn [UCOS2_module_rep]; split; entailer!.
Qed.

Lemma task_stat_masked_merge_statistics : forall environment critical saved_local sg caller saved acquired state statistics,
  UCOS2_state_inv sg (replace_StatsS statistics state) ->
  statistics_rep sg statistics **
    task_stat_masked_statistics_frame environment critical saved_local sg caller saved acquired state |--
  task_suspend_masked environment critical saved_local sg caller saved acquired (replace_StatsS statistics state).
Proof.
  intros * Hvalid; unfold task_suspend_masked, task_stat_masked_statistics_frame; Intros.
  rewrite task_stat_call_resources_replace_statistics.
  pose proof (UCOS2_inv_merge_updated_module sg state
    (replace_StatsS statistics state) StatisticsModule Hvalid ltac:(reflexivity)) as Hmerge.
  change (statistics_rep sg statistics ** UCOS2_raw_rep_missing_module sg state StatisticsModule |--
    UCOS2_inv sg (replace_StatsS statistics state)) in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma task_stat_save_post_context : forall environment critical saved_local sg frame operation caller mask saved before X,
  task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatAcquire operation) caller mask) before X ->
  task_suspend_save_history_post environment critical saved_local sg caller mask saved before ** frame |--
  EX returned acquired,
    task_stat_masked_checkpoint environment critical saved_local sg frame
      (TaskStatProtected operation saved acquired) returned mask saved acquired acquired X.
Proof.
  intros * Hcontext; unfold task_suspend_save_history_post; Intros returned acquired.
  match goal with H : task_suspend_save_observation _ _ _ _ _ _ _ _ /\ _ |- _ => destruct H as [Hobservation Heffect] end.
  assert (Hnext : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatProtected operation saved acquired) returned mask) acquired X).
  { eapply task_stat_context_step; [exact Hcontext|apply task_stat_step_save; assumption]. }
  Exists returned acquired; unfold task_stat_masked_checkpoint; entailer!.
Qed.

Lemma task_stat_restore_post_context : forall environment critical saved_local sg frame operation sample caller mask saved acquired released X,
  task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatRelease operation saved acquired sample) caller mask) released X ->
  task_suspend_restore_history_post environment critical saved_local sg caller saved released ** frame |--
  EX returned current,
    task_stat_closed_checkpoint environment critical saved_local sg frame
      (task_stat_after_release operation sample) returned (armv7a_irq_fiq_mask saved) current X.
Proof.
  intros * Hcontext; unfold task_suspend_restore_history_post; Intros returned current.
  match goal with H : task_suspend_restore_observation _ _ _ _ _ _ /\ _ |- _ => destruct H as [Hobservation Heffect] end.
  assert (Hnext : task_stat_context environment critical saved_local sg frame
    (task_stat_at (task_stat_after_release operation sample) returned (armv7a_irq_fiq_mask saved)) current X).
  { eapply task_stat_context_step; [exact Hcontext|apply task_stat_step_restore; assumption]. }
  Exists returned current; unfold task_stat_closed_checkpoint; entailer!.
Qed.

Lemma task_stat_protected_step_resources : forall environment critical saved_local sg frame operation caller mask saved acquired state X before after sample,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatProtected operation saved acquired) caller mask) state X ->
  (task_suspend_masked environment critical saved_local sg caller saved acquired state ** frame) before ->
  task_stat_protected_fragment sg operation state.(StatsState) sample before after ->
  let current := replace_StatsS (task_stat_protected_statistics operation state.(StatsState)) state in
  task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatRelease operation saved acquired sample) caller mask) current X /\
  (task_suspend_masked environment critical saved_local sg caller saved acquired current ** frame) after.
Proof.
  intros * Henabled Hcontext Hbefore Hsource current.
  assert (Hsplit : task_suspend_masked environment critical saved_local sg caller saved acquired state ** frame |--
    UCOS2_inv sg state **
      (critical_region_masked environment.(task_stack_call_platform) critical sg
        (task_suspend_view caller).(os_execution_invocation) (task_suspend_view caller).(os_execution_origin) saved acquired **
       task_suspend_call_resources environment saved_local sg caller state ** frame)).
  { unfold task_suspend_masked; entailer!. }
  destruct (task_stat_protected_fragment_resources sg operation state _ before after sample Henabled
    (Hsplit _ Hbefore) Hsource) as [Hsample Hafter].
  split.
  - subst sample; eapply task_stat_context_step; [exact Hcontext|apply task_stat_step_protected].
  - assert (Hmerge : UCOS2_inv sg current **
      (critical_region_masked environment.(task_stack_call_platform) critical sg
        (task_suspend_view caller).(os_execution_invocation) (task_suspend_view caller).(os_execution_origin) saved acquired **
       task_suspend_call_resources environment saved_local sg caller state ** frame) |--
      task_suspend_masked environment critical saved_local sg caller saved acquired current ** frame).
    { unfold task_suspend_masked; unfold current; rewrite task_stat_call_resources_replace_statistics; entailer!. }
    apply Hmerge; exact Hafter.
Qed.

Lemma task_stat_delay_call_pre : forall environment critical saved_local sg frame stage caller mask ticks next state X,
  task_stat_delay_instruction stage = Some (ticks, next) ->
  task_stat_context environment critical saved_local sg frame (task_stat_at stage caller mask) state X ->
  task_suspend_closed environment critical saved_local sg caller mask state ** frame |--
  time_dly_call_pre environment critical saved_local sg caller mask ticks state frame.
Proof.
  intros * Hinstruction Hcontext.
  pose proof (proj2 (task_stat_context_current _ _ _ _ _ _ _ _ Hcontext)) as Hadmission.
  unfold task_stat_call_admission in Hadmission; cbn in Hadmission; rewrite Hinstruction in Hadmission.
  unfold time_dly_call_pre; entailer!.
Qed.

Lemma task_stat_suspend_self_no_argument_error : forall sg,
  task_stat_configuration sg -> task_suspend_argument_error sg sg.(osPrioSelf) = None.
Proof.
  intros sg [Hvalid Hrest]; apply task_suspend_argument_error_self.
  unfold valid_stable_glob_vars in Hvalid; lia.
Qed.

Lemma task_stat_suspend_call_pre : forall environment critical saved_local sg frame caller mask state X,
  task_stat_configuration sg ->
  task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatSelfSuspend caller mask) state X ->
  task_suspend_closed environment critical saved_local sg caller mask state ** frame |--
  task_suspend_call_pre environment critical saved_local sg caller mask state sg.(osPrioSelf) frame.
Proof.
  intros * Hconfiguration Hcontext.
  pose proof (proj2 (task_stat_context_current _ _ _ _ _ _ _ _ Hcontext)) as Hadmission.
  cbn [task_stat_call_admission task_stat_delay_instruction task_stat_at task_stat_stage task_stat_caller task_stat_mask] in Hadmission.
  unfold task_stat_suspend_admission in Hadmission.
  pose proof (task_stat_suspend_self_no_argument_error sg Hconfiguration) as Hargument.
  unfold task_suspend_call_pre; rewrite Hargument.
  destruct Hconfiguration as [Hvalid [Hstatistics [[Hchecks [Hlowest Hself]] Hprofile]]].
  entailer!; tauto || lia.
Qed.

Lemma task_stat_closed_load_value_eq : forall environment critical saved_local sg caller mask state frame field heap observed,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (task_suspend_closed environment critical saved_local sg caller mask state ** frame) heap ->
  statistics_load_fragment sg field observed heap ->
  observed = statistics_load_value field state.(StatsState).
Proof.
  intros * Henabled Hheap Hload.
  pose proof (task_stat_closed_load environment critical saved_local sg caller mask state frame field heap Henabled Hheap) as Hexpected.
  destruct field; [eapply KernelHeapObservation.uchar_load_deterministic|eapply KernelHeapObservation.pointer_load_deterministic]; eassumption.
Qed.

Lemma task_stat_ready_read_context : forall environment critical saved_local sg frame caller mask state X heap observed,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatReady caller mask) state X ->
  (task_suspend_closed environment critical saved_local sg caller mask state ** frame) heap ->
  statistics_load_fragment sg StatisticsReadyField observed heap ->
  task_stat_context environment critical saved_local sg frame
    (task_stat_at (if Z.eqb observed 0 then TaskStatReadyDelay else TaskStatScaleLoad) caller mask) state X.
Proof.
  intros * Henabled Hcontext Hheap Hload.
  pose proof (task_stat_closed_load_value_eq _ _ _ _ _ _ _ _ _ _ _ Henabled Hheap Hload) as Hvalue.
  subst observed; cbn [statistics_load_value].
  replace (if (if statReady (StatsState state) then 1 else 0) =? 0 then TaskStatReadyDelay else TaskStatScaleLoad)
    with (if statReady (StatsState state) then TaskStatScaleLoad else TaskStatReadyDelay)
    by (destruct (statReady (StatsState state)); reflexivity).
  eapply task_stat_context_step; [exact Hcontext|apply task_stat_step_ready].
Qed.

Lemma task_stat_zero_read_context : forall environment critical saved_local sg frame caller mask state X heap observed,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatZeroTest caller mask) state X ->
  (task_suspend_closed environment critical saved_local sg caller mask state ** frame) heap ->
  statistics_load_fragment sg StatisticsMaxField observed heap ->
  task_stat_context environment critical saved_local sg frame
    (task_stat_at (if Z.eqb observed 0 then TaskStatZeroUsage else TaskStatAcquire TaskStatInitialize) caller mask) state X.
Proof.
  intros * Henabled Hcontext Hheap Hload.
  pose proof (task_stat_closed_load_value_eq _ _ _ _ _ _ _ _ _ _ _ Henabled Hheap Hload) as Hvalue.
  subst observed; eapply task_stat_context_step; [exact Hcontext|apply task_stat_step_zero_test].
Qed.

(** The explicit load/interval/store composition is consumed by the scaling
    source boundary.  The stored quotient is calculated from the actual
    earlier load even if the permitted interval changed Max in between. *)
Lemma task_stat_scale_load_interval_store : forall environment critical saved_local sg frame caller returned mask
  before middle X read_heap store_heap after_heap loaded,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatScaleLoad caller mask) before X ->
  (task_suspend_closed environment critical saved_local sg caller mask before ** frame) read_heap ->
  statistics_load_fragment sg StatisticsMaxField loaded read_heap ->
  critical_region_interval critical sg (task_suspend_view caller).(os_execution_invocation) before middle ->
  task_suspend_same_call returned caller ->
  (task_suspend_closed environment critical saved_local sg returned mask middle ** frame) store_heap ->
  statistics_store_fragment sg StatisticsCalibrationField (loaded / 100) store_heap after_heap ->
  let current := replace_StatsS (statistics_store_state StatisticsCalibrationField (loaded / 100) middle.(StatsState)) middle in
  task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatZeroTest returned mask) current X /\
  (task_suspend_closed environment critical saved_local sg returned mask current ** frame) after_heap.
Proof.
  intros * Henabled Hcontext Hread_heap Hload Hinterval Hsame Hstore_heap Hstore current.
  pose proof (task_stat_closed_load_value_eq _ _ _ _ _ _ _ _ _ _ _ Henabled Hread_heap Hload) as Hloaded.
  assert (Hloaded_context : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatScaleStore loaded) caller mask) before X).
  { rewrite Hloaded; eapply task_stat_context_step; [exact Hcontext|apply task_stat_step_scale_load]. }
  assert (Hmiddle : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatScaleStore loaded) returned mask) middle X).
  { eapply task_stat_context_step; [exact Hloaded_context|].
    apply task_stat_step_interference; [reflexivity|exact Hinterval|exact Hsame]. }
  eapply task_stat_store_step_resources; [exact Henabled|exact Hmiddle|reflexivity|exact Hstore_heap|exact Hstore].
Qed.

(** Separate source stores with an explicit actual environment endpoint.
    No equality identifies the post-usage heap with the later calibration
    heap; the second store preserves usage from the latter heap. *)
Lemma task_stat_usage_interval_recalibration : forall environment critical saved_local sg frame caller returned mask
  sample before middle X before_heap usage_heap middle_heap after_heap,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  task_stat_needs_recalibration sample = true ->
  task_stat_context environment critical saved_local sg frame (task_stat_at (TaskStatUsage sample) caller mask) before X ->
  (task_suspend_closed environment critical saved_local sg caller mask before ** frame) before_heap ->
  statistics_store_fragment sg StatisticsUsageField (task_stat_sample_usage sample) before_heap usage_heap ->
  critical_region_interval critical sg (task_suspend_view caller).(os_execution_invocation)
    (replace_StatsS (statistics_store_state StatisticsUsageField (task_stat_sample_usage sample) before.(StatsState)) before) middle ->
  task_suspend_same_call returned caller ->
  (task_suspend_closed environment critical saved_local sg returned mask middle ** frame) middle_heap ->
  statistics_store_fragment sg StatisticsCalibrationField (sample.(sampleRun) / 100) middle_heap after_heap ->
  let current := replace_StatsS (statistics_store_state StatisticsCalibrationField (sample.(sampleRun) / 100) middle.(StatsState)) middle in
  task_stat_context environment critical saved_local sg frame (task_stat_at TaskStatHook returned mask) current X /\
  (task_suspend_closed environment critical saved_local sg returned mask current ** frame) after_heap.
Proof.
  intros * Henabled Hrecalibrate Hcontext Hbefore Husage Hinterval Hsame Hmiddle Hstore current.
  assert (Hinstruction : task_stat_store_instruction (TaskStatUsage sample) =
    Some (StatisticsUsageField, task_stat_sample_usage sample, TaskStatRecalibrate sample)).
  { cbn [task_stat_store_instruction]; unfold task_stat_after_usage; rewrite Hrecalibrate; reflexivity. }
  destruct (task_stat_store_step_resources environment critical saved_local sg frame (TaskStatUsage sample)
    caller mask before X StatisticsUsageField (task_stat_sample_usage sample) (TaskStatRecalibrate sample)
    before_heap usage_heap Henabled Hcontext Hinstruction Hbefore Husage) as [Hwritten Hwritten_heap].
  assert (Hnext : task_stat_context environment critical saved_local sg frame
    (task_stat_at (TaskStatRecalibrate sample) returned mask) middle X).
  { eapply task_stat_context_step; [exact Hwritten|].
    apply task_stat_step_interference; [reflexivity|exact Hinterval|exact Hsame]. }
  eapply task_stat_store_step_resources; [exact Henabled|exact Hnext|reflexivity|exact Hmiddle|exact Hstore].
Qed.
