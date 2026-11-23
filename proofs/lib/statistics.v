Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only this module owns the five statistics cells.  The statistics and
    idle tasks themselves remain Task-owned.  A StatisticsSample is an
    call-local value snapshot, not a second global owner or a caller ID. *)
Definition valid_statistics_state (s : StatisticsState) : Prop :=
  0 <= s.(idleCtr) < 4294967296 /\
  0 <= s.(idleCtrMax) < 4294967296 /\
  0 <= s.(idleCtrRun) < 4294967296 /\ 0 <= s.(cpuUsage) < 256.
Definition valid_statistics_sample (v : StatisticsSample) : Prop :=
  0 <= v.(sampleRun) < 4294967296 /\ 0 <= v.(sampleDivisor) < 4294967296.

Definition statistics_rep (sg : StableGlobVars) (s : StatisticsState) : Assertion :=
  sg.(g_OSIdleCtr) # UInt |-> s.(idleCtr) **
  (if sg.(osKernelConfig).(cfgStatisticsEnabled) then
    sg.(g_OSIdleCtrMax) # UInt |-> s.(idleCtrMax) **
    sg.(g_OSIdleCtrRun) # UInt |-> s.(idleCtrRun) **
    sg.(g_OSCPUUsage) # UChar |-> s.(cpuUsage) **
    sg.(g_OSStatRdy) # UChar |-> (if s.(statReady) then 1 else 0)
   else emp).
Definition valid_statistics_configuration (sg : StableGlobVars) (s : StatisticsState) : Prop :=
  valid_statistics_state s /\
  if sg.(osKernelConfig).(cfgStatisticsEnabled) then True else
    s.(idleCtrMax) = 0 /\ s.(idleCtrRun) = 0 /\ s.(cpuUsage) = 0 /\
    s.(statReady) = false.
Definition statistics_inv (sg : StableGlobVars) (s : StatisticsState) : Assertion :=
  coq_prop (valid_statistics_configuration sg s) && statistics_rep sg s.
Definition statistics_initial : StatisticsState :=
  {| idleCtr := 0; idleCtrMax := 0; idleCtrRun := 0; cpuUsage := 0;
     statReady := false |}.
Lemma statistics_initial_valid : valid_statistics_state statistics_initial.
Proof. unfold valid_statistics_state, statistics_initial; simpl; lia. Qed.
Lemma statistics_initial_configuration_valid : forall sg,
  valid_statistics_configuration sg statistics_initial.
Proof.
  intro sg; split; [apply statistics_initial_valid|].
  destruct (cfgStatisticsEnabled (osKernelConfig sg)); simpl; auto.
Qed.

Definition statistics_set_counter (s : StatisticsState) (n : Z) : StatisticsState :=
  {| idleCtr := kernel_u32 n; idleCtrMax := s.(idleCtrMax);
     idleCtrRun := s.(idleCtrRun); cpuUsage := s.(cpuUsage);
     statReady := s.(statReady) |}.
Definition statistics_idle_step (s : StatisticsState) : StatisticsState :=
  statistics_set_counter s (s.(idleCtr) + 1).
Definition statistics_reset_counter (s : StatisticsState) : StatisticsState :=
  statistics_set_counter s 0.
Definition statistics_calibrate (s : StatisticsState) : StatisticsState :=
  {| idleCtr := s.(idleCtr); idleCtrMax := s.(idleCtr);
     idleCtrRun := s.(idleCtrRun); cpuUsage := s.(cpuUsage);
     statReady := true |}.
Definition statistics_scale_divisor (s : StatisticsState) : StatisticsState :=
  {| idleCtr := s.(idleCtr); idleCtrMax := s.(idleCtrMax) / 100;
     idleCtrRun := s.(idleCtrRun); cpuUsage := s.(cpuUsage);
     statReady := s.(statReady) |}.
Definition statistics_capture (s : StatisticsState)
  : StatisticsSample * StatisticsState :=
  ({| sampleRun := s.(idleCtr); sampleDivisor := s.(idleCtrMax) |},
   {| idleCtr := s.(idleCtr); idleCtrMax := s.(idleCtrMax);
      idleCtrRun := s.(idleCtr); cpuUsage := s.(cpuUsage);
      statReady := s.(statReady) |}).

Lemma statistics_set_counter_preserves_validity : forall s n,
  valid_statistics_state s -> valid_statistics_state (statistics_set_counter s n).
Proof.
  intros s n [Hc [Hm [Hr Hu]]]; unfold valid_statistics_state, statistics_set_counter;
    simpl; split; [apply kernel_u32_in_range|auto].
Qed.
Lemma statistics_idle_step_preserves_validity : forall s,
  valid_statistics_state s -> valid_statistics_state (statistics_idle_step s).
Proof. intros; apply statistics_set_counter_preserves_validity; assumption. Qed.
Lemma statistics_idle_step_preserves_configuration : forall sg s,
  valid_statistics_configuration sg s -> valid_statistics_configuration sg (statistics_idle_step s).
Proof.
  intros sg s [Hv Hcfg]; split; [apply statistics_idle_step_preserves_validity; exact Hv|].
  unfold statistics_idle_step, statistics_set_counter; simpl; exact Hcfg.
Qed.
Lemma statistics_reset_counter_preserves_validity : forall s,
  valid_statistics_state s -> valid_statistics_state (statistics_reset_counter s).
Proof. intros; apply statistics_set_counter_preserves_validity; assumption. Qed.
Lemma statistics_calibrate_preserves_validity : forall s,
  valid_statistics_state s -> valid_statistics_state (statistics_calibrate s).
Proof. intros s H; unfold valid_statistics_state, statistics_calibrate in *; simpl; tauto. Qed.

Lemma statistics_div100_in_range : forall n,
  0 <= n < 4294967296 -> 0 <= n / 100 < 4294967296.
Proof.
  intros n H; split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; lia.
Qed.
Lemma statistics_scale_divisor_preserves_validity : forall s,
  valid_statistics_state s -> valid_statistics_state (statistics_scale_divisor s).
Proof.
  intros s [Hc [Hm [Hr Hu]]]; unfold valid_statistics_state, statistics_scale_divisor;
    simpl; split; [exact Hc|]. split; [apply statistics_div100_in_range; exact Hm|auto].
Qed.
Lemma statistics_capture_preserves_validity : forall s,
  valid_statistics_state s ->
  valid_statistics_sample (fst (statistics_capture s)) /\
  valid_statistics_state (snd (statistics_capture s)).
Proof.
  intros s H; unfold statistics_capture, valid_statistics_sample,
    valid_statistics_state in *; simpl; tauto.
Qed.

(** The original V2.93.01 source narrows both the quotient and the assigned
    signed usage.  kernel_s8 is the selected ABI's signed-byte conversion.
    None exposes C division by zero; it is not silently made a valid step. *)
Definition statistics_original_usage (quotient : Z) : Z :=
  kernel_s8 (100 - kernel_s8 quotient).
Definition statistics_original_update (s : StatisticsState) : option StatisticsState :=
  if Z.eqb s.(idleCtrMax) 0 then None else
  let usage := statistics_original_usage (s.(idleCtrRun) / s.(idleCtrMax)) in
  Some {| idleCtr := s.(idleCtr);
          idleCtrMax := if 0 <=? usage then s.(idleCtrMax) else s.(idleCtrRun) / 100;
          idleCtrRun := s.(idleCtrRun);
          cpuUsage := if 0 <=? usage then kernel_u8 usage else 0;
          statReady := s.(statReady) |}.

Lemma statistics_original_zero_divisor : forall s,
  s.(idleCtrMax) = 0 -> statistics_original_update s = None.
Proof. intros s H; unfold statistics_original_update; rewrite H; reflexivity. Qed.
Lemma statistics_original_usage_can_exceed_percentage :
  statistics_original_usage 229 = 127.
Proof. reflexivity. Qed.
Lemma statistics_original_preserves_machine_ranges : forall s post,
  valid_statistics_state s -> statistics_original_update s = Some post ->
  valid_statistics_state post.
Proof.
  intros s post [Hc [Hm [Hr Hu]]] Hstep; unfold statistics_original_update in Hstep.
  destruct (Z.eqb (idleCtrMax s) 0); [discriminate|].
  inversion Hstep; subst; unfold valid_statistics_state; simpl.
  split; [exact Hc|].
  destruct (0 <=? statistics_original_usage (idleCtrRun s / idleCtrMax s)).
  - split; [exact Hm|]. split; [exact Hr|apply kernel_u8_in_range].
  - split; [apply statistics_div100_in_range; exact Hr|]. split; [exact Hr|lia].
Qed.

(** This relation follows source_variants/statistics-sampling/os_core.patch:
    the denominator and run are captured together, zero is guarded on every
    iteration, and the full-width quotient is tested before narrowing.
    Recalibration uses that same sample even if globals changed meanwhile. *)
Definition statistics_repaired_update (v : StatisticsSample) (s : StatisticsState)
  : StatisticsState :=
  let zero := Z.eqb v.(sampleDivisor) 0 in
  let q := v.(sampleRun) / v.(sampleDivisor) in
  {| idleCtr := s.(idleCtr);
     idleCtrMax := if zero then s.(idleCtrMax) else
       if q <=? 100 then s.(idleCtrMax) else v.(sampleRun) / 100;
     idleCtrRun := s.(idleCtrRun);
     cpuUsage := if zero then 0 else if q <=? 100 then kernel_u8 (100 - q) else 0;
     statReady := s.(statReady) |}.

Lemma statistics_repaired_cpu_in_percentage_range : forall v s,
  valid_statistics_sample v -> 0 <= (statistics_repaired_update v s).(cpuUsage) <= 100.
Proof.
  intros v s [Hr Hd].
  change (0 <= (if Z.eqb v.(sampleDivisor) 0 then 0 else
    if v.(sampleRun) / v.(sampleDivisor) <=? 100 then
      kernel_u8 (100 - v.(sampleRun) / v.(sampleDivisor)) else 0) <= 100).
  destruct (Z.eqb (sampleDivisor v) 0) eqn:Hz; [lia|].
  apply Z.eqb_neq in Hz.
  assert (Hq : 0 <= sampleRun v / sampleDivisor v) by (apply Z.div_pos; lia).
  destruct (sampleRun v / sampleDivisor v <=? 100) eqn:Hle; [|lia].
  apply Z.leb_le in Hle; rewrite kernel_u8_identity; lia.
Qed.
Lemma statistics_repaired_preserves_validity : forall v s,
  valid_statistics_sample v -> valid_statistics_state s ->
  valid_statistics_state (statistics_repaired_update v s).
Proof.
  intros v s Hv [Hc [Hm [Hr Hu]]].
  pose proof (statistics_repaired_cpu_in_percentage_range v s Hv) as Husage.
  unfold valid_statistics_state; split; [exact Hc|]. split.
  - unfold statistics_repaired_update; simpl.
    destruct (Z.eqb (sampleDivisor v) 0); [exact Hm|].
    destruct (sampleRun v / sampleDivisor v <=? 100); [exact Hm|].
    apply statistics_div100_in_range; exact (proj1 Hv).
  - split; [exact Hr|lia].
Qed.
Lemma statistics_repaired_zero_keeps_calibration : forall v s,
  v.(sampleDivisor) = 0 ->
  (statistics_repaired_update v s).(cpuUsage) = 0 /\
  (statistics_repaired_update v s).(idleCtrMax) = s.(idleCtrMax).
Proof. intros v s H; unfold statistics_repaired_update; simpl; rewrite H; auto. Qed.
Lemma statistics_repaired_recalibrates_same_sample : forall v s,
  v.(sampleDivisor) <> 0 -> 100 < v.(sampleRun) / v.(sampleDivisor) ->
  (statistics_repaired_update v s).(cpuUsage) = 0 /\
  (statistics_repaired_update v s).(idleCtrMax) = v.(sampleRun) / 100.
Proof.
  intros v s Hd Hq; unfold statistics_repaired_update; simpl.
  destruct (Z.eqb (sampleDivisor v) 0) eqn:Hz; [apply Z.eqb_eq in Hz; contradiction|].
  destruct (sampleRun v / sampleDivisor v <=? 100) eqn:Hl;
    [apply Z.leb_le in Hl; lia|auto].
Qed.

Lemma statistics_original_repaired_agree_normal : forall s v,
  valid_statistics_state s -> 0 < s.(idleCtrMax) ->
  s.(idleCtrRun) / s.(idleCtrMax) <= 100 ->
  v.(sampleRun) = s.(idleCtrRun) -> v.(sampleDivisor) = s.(idleCtrMax) ->
  statistics_original_update s = Some (statistics_repaired_update v s).
Proof.
  intros s v [Hc [Hm [Hr Hu]]] Hmax Hq Hrun Hdiv.
  assert (Hq0 : 0 <= idleCtrRun s / idleCtrMax s) by (apply Z.div_pos; lia).
  assert (Hz : Z.eqb (idleCtrMax s) 0 = false) by (apply Z.eqb_neq; lia).
  assert (Hle : (idleCtrRun s / idleCtrMax s <=? 100) = true) by (apply Z.leb_le; exact Hq).
  assert (Husage : statistics_original_usage (idleCtrRun s / idleCtrMax s) =
    100 - idleCtrRun s / idleCtrMax s).
  { unfold statistics_original_usage.
    rewrite (kernel_s8_identity (idleCtrRun s / idleCtrMax s) ltac:(lia)).
    apply kernel_s8_identity; lia. }
  assert (Hnonneg : (0 <=? statistics_original_usage (idleCtrRun s / idleCtrMax s)) = true).
  { rewrite Husage; apply Z.leb_le; lia. }
  unfold statistics_original_update, statistics_repaired_update.
  rewrite Hrun, Hdiv, Hz, Hle, Hnonneg, Husage; reflexivity.
Qed.

Definition statistics_rep_without_usage (sg : StableGlobVars) (s : StatisticsState)
  : Assertion :=
  sg.(g_OSIdleCtr) # UInt |-> s.(idleCtr) **
  sg.(g_OSIdleCtrMax) # UInt |-> s.(idleCtrMax) **
  sg.(g_OSIdleCtrRun) # UInt |-> s.(idleCtrRun) **
  sg.(g_OSStatRdy) # UChar |-> (if s.(statReady) then 1 else 0).
Lemma statistics_rep_split_usage : forall sg s,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_rep sg s |--
  sg.(g_OSCPUUsage) # UChar |-> s.(cpuUsage) **
  statistics_rep_without_usage sg s.
Proof. intros; unfold statistics_rep, statistics_rep_without_usage; rewrite H; entailer!. Qed.
Lemma statistics_rep_merge_usage : forall sg s,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  sg.(g_OSCPUUsage) # UChar |-> s.(cpuUsage) **
  statistics_rep_without_usage sg s |-- statistics_rep sg s.
Proof. intros; unfold statistics_rep, statistics_rep_without_usage; rewrite H; entailer!. Qed.
Lemma statistics_rep_merge_updated_usage : forall sg s post,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  s.(idleCtr) = post.(idleCtr) -> s.(idleCtrMax) = post.(idleCtrMax) ->
  s.(idleCtrRun) = post.(idleCtrRun) -> s.(statReady) = post.(statReady) ->
  sg.(g_OSCPUUsage) # UChar |-> post.(cpuUsage) **
  statistics_rep_without_usage sg s |-- statistics_rep sg post.
Proof.
  intros sg s post Hcfg Hc Hm Hr Hb.
  unfold statistics_rep, statistics_rep_without_usage; rewrite Hcfg, Hc, Hm, Hr, Hb; entailer!.
Qed.
