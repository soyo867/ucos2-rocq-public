Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.statistics.
Require Export Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.lib.ucos2_state_machine.
Require Export Ucos2Verify.lib.statistics_execution.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
From SimpleC.SL Require Import Mem SeparationLogic.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_TaskIdle is an internal, nonreturning task entry.  The contract below
    records finite prefixes, not termination, idle-time accuracy or fairness.
    Each iteration has the actual Save acquisition, unsigned store, Restore
    return, and external port-hook return.  Only the store is protected. *)
Definition task_idle_counter (state : UCOS2_Verify_State) : Z :=
  state.(StatsState).(idleCtr).

Definition task_idle_counter_after (state : UCOS2_Verify_State) : Z :=
  kernel_u32 (task_idle_counter state + 1).

Definition task_idle_update (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_StatsS (statistics_idle_step state.(StatsState)) state.

(** This parameter describes NORMAL RETURNS of the actual OSTaskIdleHook
    supplied by the selected port/application.  There is no implementation
    in this source input.  The C declaration below consumes [closed] at its
    actual input and returns [closed] at this relation's actual output/mask.
    Instantiating that declaration is an external implementation obligation,
    not a theorem that an empty App_TaskIdleHook was linked.  The relation
    contains neither the preceding counter store nor the task loop. *)
Definition TaskIdleHookRelation : Type :=
  StableGlobVars -> nat -> TaskInvocationOrigin ->
    Z -> UCOS2_Verify_State -> Z -> UCOS2_Verify_State -> Prop.

Definition task_idle_hook_returns (hook : TaskIdleHookRelation)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (mask : Z) (before : UCOS2_Verify_State) (next_mask : Z)
  (after : UCOS2_Verify_State) : Prop :=
  hook sg invocation origin mask before next_mask after.

Record TaskIdleIteration : Type := {
  idle_iteration_mask : Z;
  idle_iteration_before : UCOS2_Verify_State;
  idle_iteration_saved : Z;
  idle_iteration_acquired : UCOS2_Verify_State;
  idle_iteration_restored : UCOS2_Verify_State;
  idle_iteration_next_mask : Z;
  idle_iteration_after : UCOS2_Verify_State;
}.

Definition task_idle_iteration (critical : CriticalRegionResources)
  (hook : TaskIdleHookRelation) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (step : TaskIdleIteration) : Prop :=
  critical_region_interval critical sg invocation
    step.(idle_iteration_before) step.(idle_iteration_acquired) /\
  interrupt_saved_value step.(idle_iteration_mask) step.(idle_iteration_saved) /\
  critical_region_interval critical sg invocation
    (task_idle_update step.(idle_iteration_acquired)) step.(idle_iteration_restored) /\
  hook sg invocation origin step.(idle_iteration_mask) step.(idle_iteration_restored)
    step.(idle_iteration_next_mask) step.(idle_iteration_after).

Inductive task_idle_prefix (critical : CriticalRegionResources)
  (hook : TaskIdleHookRelation) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (initial_mask : Z) (initial : UCOS2_Verify_State)
  : list TaskIdleIteration -> Z -> UCOS2_Verify_State -> Prop :=
| task_idle_prefix_empty :
    task_idle_prefix critical hook sg invocation origin initial_mask initial
      [] initial_mask initial
| task_idle_prefix_append : forall history step,
    task_idle_prefix critical hook sg invocation origin initial_mask initial
      history step.(idle_iteration_mask) step.(idle_iteration_before) ->
    task_idle_iteration critical hook sg invocation origin step ->
    task_idle_prefix critical hook sg invocation origin initial_mask initial
      (history ++ [step]) step.(idle_iteration_next_mask) step.(idle_iteration_after).

Definition task_idle_written (critical : CriticalRegionResources)
  (hook : TaskIdleHookRelation) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (initial_mask : Z) (initial : UCOS2_Verify_State)
  (history : list TaskIdleIteration) (mask saved : Z)
  (before acquired checkpoint : UCOS2_Verify_State) : Prop :=
  task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before /\
  critical_region_interval critical sg invocation before acquired /\
  interrupt_saved_value mask saved /\ checkpoint = task_idle_update acquired.

Definition task_idle_extend_history (history : list TaskIdleIteration)
  (mask saved : Z) (before acquired restored : UCOS2_Verify_State)
  (next_mask : Z) (after : UCOS2_Verify_State) : list TaskIdleIteration :=
  history ++ [{| idle_iteration_mask := mask;
    idle_iteration_before := before; idle_iteration_saved := saved;
    idle_iteration_acquired := acquired; idle_iteration_restored := restored;
    idle_iteration_next_mask := next_mask; idle_iteration_after := after |}].

Lemma task_idle_written_hook_extends_prefix :
  forall critical hook sg invocation origin initial_mask initial history mask saved
    before acquired checkpoint restored next_mask after,
  task_idle_written critical hook sg invocation origin initial_mask initial
    history mask saved before acquired checkpoint ->
  critical_region_interval critical sg invocation checkpoint restored ->
  hook sg invocation origin mask restored next_mask after ->
  task_idle_prefix critical hook sg invocation origin initial_mask initial
    (task_idle_extend_history history mask saved before acquired restored next_mask after)
    next_mask after.
Proof.
  intros critical hook sg invocation origin initial_mask initial history mask saved
    before acquired checkpoint restored next_mask after
    [Hprefix [Hacquire [Hsaved ->]]] Hrestore Hhook.
  unfold task_idle_extend_history; apply task_idle_prefix_append.
  - exact Hprefix.
  - unfold task_idle_iteration; simpl.
    exact (conj Hacquire (conj Hsaved (conj Hrestore Hhook))).
Qed.

Lemma task_idle_counter_after_uint : forall state,
  unsigned_last_nbits (task_idle_counter state + 1) 32 = task_idle_counter_after state.
Proof.
  intro state; unfold task_idle_counter_after, kernel_u32, unsigned_last_nbits.
  reflexivity.
Qed.

Lemma task_idle_counter_wraps : forall state,
  task_idle_counter state = 4294967295 -> task_idle_counter_after state = 0.
Proof. intros state H; unfold task_idle_counter_after; rewrite H; reflexivity. Qed.

Lemma task_idle_update_preserves_validity : forall sg state,
  UCOS2_state_inv sg state -> UCOS2_state_inv sg (task_idle_update state).
Proof.
  intros sg state Hvalid.
  exact (selected_transition_valid sg statistics_modules _
    (statistics_idle_selected_transition sg) state (task_idle_update state) Hvalid eq_refl).
Qed.

(** The structural remainder removes only OSIdleCtr.  It does not contain
    a second copy of the counter or a stale validity predicate. *)
Definition task_idle_statistics_rest (sg : StableGlobVars)
  (state : StatisticsState) : Assertion :=
  if sg.(osKernelConfig).(cfgStatisticsEnabled) then
    sg.(g_OSIdleCtrMax) # UInt |-> state.(idleCtrMax) **
    sg.(g_OSIdleCtrRun) # UInt |-> state.(idleCtrRun) **
    sg.(g_OSCPUUsage) # UChar |-> state.(cpuUsage) **
    sg.(g_OSStatRdy) # UChar |-> (if state.(statReady) then 1 else 0)
  else emp.

Lemma task_idle_statistics_split_counter : forall sg state,
  statistics_rep sg state |--
  sg.(g_OSIdleCtr) # UInt |-> state.(idleCtr) ** task_idle_statistics_rest sg state.
Proof. intros; unfold statistics_rep, task_idle_statistics_rest; entailer!. Qed.

Lemma task_idle_statistics_merge_counter : forall sg state,
  sg.(g_OSIdleCtr) # UInt |-> state.(idleCtr) ** task_idle_statistics_rest sg state |--
  statistics_rep sg state.
Proof. intros; unfold statistics_rep, task_idle_statistics_rest; entailer!. Qed.

Lemma task_idle_statistics_merge_updated_counter : forall sg state,
  sg.(g_OSIdleCtr) # UInt |-> kernel_u32 (state.(idleCtr) + 1) **
    task_idle_statistics_rest sg state |-- statistics_rep sg (statistics_idle_step state).
Proof.
  intros; unfold statistics_rep, statistics_idle_step, statistics_set_counter,
    task_idle_statistics_rest; simpl; entailer!.
Qed.

Lemma task_idle_missing_statistics_eq : forall sg state,
  UCOS2_raw_rep_missing_statistics sg state =
    UCOS2_raw_rep_missing_statistics sg (task_idle_update state).
Proof.
  intros; unfold UCOS2_raw_rep_missing_statistics.
  apply UCOS2_raw_rep_missing_module_frame.
  intros owner Howner; destruct owner; try reflexivity; contradiction.
Qed.

Lemma task_idle_inv_merge_updated_counter : forall sg state,
  UCOS2_state_inv sg state ->
  sg.(g_OSIdleCtr) # UInt |-> task_idle_counter_after state **
    task_idle_statistics_rest sg state.(StatsState) **
    UCOS2_raw_rep_missing_statistics sg state |-- UCOS2_inv sg (task_idle_update state).
Proof.
  intros sg state Hvalid.
  pose proof (task_idle_update_preserves_validity sg state Hvalid) as Hupdated.
  rewrite (UCOS2_inv_split_statistics sg (task_idle_update state)).
  rewrite <- task_idle_missing_statistics_eq.
  cbn [task_idle_update replace_StatsS StatsState].
  unfold task_idle_counter_after, task_idle_counter.
  sep_apply_l_atomic (task_idle_statistics_merge_updated_counter sg state.(StatsState)).
  entailer!.
Qed.

Definition task_idle_store_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (hook : TaskIdleHookRelation)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (initial_mask : Z) (initial : UCOS2_Verify_State)
  (history : list TaskIdleIteration) (mask saved : Z)
  (before acquired : UCOS2_Verify_State) : Assertion :=
  coq_prop (task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before /\
    critical_region_interval critical sg invocation before acquired /\
    interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired) &&
  (critical_region_masked platform critical sg invocation origin saved acquired **
   task_idle_statistics_rest sg acquired.(StatsState) **
   UCOS2_raw_rep_missing_statistics sg acquired).

Lemma task_idle_inv_split_counter :
  forall platform critical hook sg invocation origin initial_mask initial history mask saved before acquired,
  task_idle_prefix critical hook sg invocation origin initial_mask initial history mask before ->
  critical_region_interval critical sg invocation before acquired ->
  interrupt_saved_value mask saved -> UCOS2_state_inv sg acquired ->
  critical_region_masked platform critical sg invocation origin saved acquired ** UCOS2_inv sg acquired |--
  sg.(g_OSIdleCtr) # UInt |-> task_idle_counter acquired **
    task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask saved before acquired.
Proof.
  intros platform critical hook sg invocation origin initial_mask initial history mask saved before acquired
    Hprefix Hacquire Hsaved Hvalid.
  rewrite (UCOS2_inv_split_statistics sg acquired).
  unfold task_idle_counter, task_idle_store_frame.
  Intros.
  sep_apply_l_atomic (task_idle_statistics_split_counter sg acquired.(StatsState)).
  entailer!.
Qed.

Lemma task_idle_store_frame_merge_updated :
  forall platform critical hook sg invocation origin initial_mask initial history mask saved before acquired,
  sg.(g_OSIdleCtr) # UInt |-> task_idle_counter_after acquired **
    task_idle_store_frame platform critical hook sg invocation origin initial_mask initial history mask saved before acquired |--
  coq_prop (task_idle_written critical hook sg invocation origin initial_mask initial history mask saved before acquired
    (task_idle_update acquired)) &&
    mbox_accept_cpu_restore_pre platform critical sg invocation origin mask saved acquired (task_idle_update acquired).
Proof.
  intros; unfold task_idle_store_frame; Intros.
  match goal with H : task_idle_prefix _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hprefix [Hacquire [Hsaved Hvalid]]] end.
  pose proof (task_idle_update_preserves_validity sg acquired Hvalid) as Hupdated.
  sep_apply_l_atomic (task_idle_inv_merge_updated_counter sg acquired Hvalid).
  unfold task_idle_written, mbox_accept_cpu_restore_pre; entailer!.
Qed.
