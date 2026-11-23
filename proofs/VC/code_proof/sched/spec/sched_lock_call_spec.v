Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From SimpleC.SL Require Export Mem SeparationLogic.
Require Export Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.timer_execution.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Full OSSchedLock C-call specification. The existing checkpoint
    definitions remain read-only and describe the protected counter step;
    the composition below retains the source observation BEFORE Save and
    the possibly different state acquired AFTER Save. No extra kernel
    state record is introduced. *)

Definition os_sched_lock_running (state : UCOS2_Verify_State) : Z :=
  if state.(SchedState).(isRunning) then 1 else 0.

Definition os_sched_lock_ints (state : UCOS2_Verify_State) : Z :=
  state.(IntrState).(intNesting).

Definition os_sched_lock_locks (state : UCOS2_Verify_State) : Z :=
  state.(IntrState).(lockNesting).

Definition os_sched_lock_updated_locks (entry : UCOS2_Verify_State) : Z :=
  (sched_lock_state true entry.(IntrState)).(lockNesting).

Definition os_sched_lock_global_addresses (sg : StableGlobVars)
  (running ints locks : Z) : Prop :=
  running = sg.(g_OSRunning) /\ ints = sg.(g_OSIntNesting) /\
  locks = sg.(g_OSLockNesting).

(** This is the same external observation-loan specialization as OSIntExit,
    without its ISR stack, switch or entry-safety assumptions. The outside
    region lends the actual running byte. Save consumes the loan and returns
    the complete current kernel representation; Restore consumes that full
    representation and returns the loan and region handle. This interface
    is an explicit CPU/CSL trust boundary, not an ARM/BSP implementation
    theorem and not a source-state equality across the observation interval.
    Arbitrary disjoint caller resources are preserved by the frame rule. *)
Definition os_sched_lock_outside_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin mask **
  critical_region_outside_without_running critical sg invocation state.

Definition os_sched_lock_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg before) &&
  (sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
   os_sched_lock_outside_frame platform critical sg invocation origin mask before).

Definition os_sched_lock_inside_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (entry : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg invocation origin saved entry.

Lemma os_sched_lock_pre_closed_equiv : forall platform critical sg invocation origin mask before,
  os_sched_lock_pre platform critical sg invocation origin mask before --||--
    coq_prop (UCOS2_state_inv sg before) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation before).
Proof.
  intros; unfold os_sched_lock_pre, os_sched_lock_outside_frame,
    os_sched_lock_running, critical_region_outside.
  split; entailer!.
Qed.

Definition os_sched_lock_body_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  before.(SchedState).(isRunning) = true /\
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved.

(** Exact ordinary-return relation. The no-Save branch has entry=before;
    the true branch permits the certified environment interval. The only
    operation write is the shared saturating lock counter transformer.
    There is no scheduler invocation or hidden scheduling guard. *)
Definition os_sched_lock_call_relation (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat)
  (before entry final : UCOS2_Verify_State) : Prop :=
  (if before.(SchedState).(isRunning)
   then critical_region_interval critical sg invocation before entry
   else entry = before) /\
  final = os_sched_lock_checkpoint before.(SchedState).(isRunning) entry.

Definition os_sched_lock_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  EX entry, EX final,
    coq_prop (os_sched_lock_call_relation critical sg invocation before entry final /\
      UCOS2_state_inv sg final) &&
    (sg.(g_OSRunning) # UChar |-> os_sched_lock_running final **
     os_sched_lock_outside_frame platform critical sg invocation origin mask final).

Lemma os_sched_lock_post_closed_equiv : forall platform critical sg invocation origin mask before,
  os_sched_lock_post platform critical sg invocation origin mask before --||--
    (EX entry, EX final,
      coq_prop (os_sched_lock_call_relation critical sg invocation before entry final /\
        UCOS2_state_inv sg final) &&
      (interrupt_platform_running platform invocation origin mask **
       critical_region_outside critical sg invocation final)).
Proof.
  intros; unfold os_sched_lock_post, os_sched_lock_outside_frame,
    os_sched_lock_running, critical_region_outside.
  split; Intros entry final; Exists entry final; entailer!.
Qed.

Lemma os_sched_lock_checkpoint_ints_eq : forall observed entry,
  os_sched_lock_ints (os_sched_lock_checkpoint observed entry) =
  os_sched_lock_ints entry.
Proof.
  intros [] entry; unfold os_sched_lock_ints, os_sched_lock_checkpoint,
    sched_lock_state; simpl;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Lemma os_sched_lock_call_timer_public_trace : forall critical sg invocation before entry final,
  os_sched_lock_call_relation critical sg invocation before entry final ->
  timer_public_trace sg before.(TimerState) final.(TimerState).
Proof.
  intros critical sg invocation before entry final [Hinterval ->].
  unfold os_sched_lock_checkpoint; cbn [replace_IntrS TimerState].
  destruct before.(SchedState).(isRunning) eqn:Hrunning.
  - eapply critical_region_interval_timer_public_trace; exact Hinterval.
  - subst entry; constructor.
Qed.

Lemma os_sched_lock_updated_locks_eq : forall entry,
  os_sched_lock_updated_locks entry =
    if os_sched_lock_ints entry =? 0 then
      if os_sched_lock_locks entry <? 255
      then os_sched_lock_locks entry + 1 else os_sched_lock_locks entry
    else os_sched_lock_locks entry.
Proof.
  intro entry; unfold os_sched_lock_updated_locks, os_sched_lock_ints,
    os_sched_lock_locks, sched_lock_state;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Lemma os_sched_lock_call_relation_total : forall critical sg invocation before,
  exists entry final, os_sched_lock_call_relation critical sg invocation before entry final.
Proof.
  intros; exists before, (os_sched_lock_checkpoint before.(SchedState).(isRunning) before).
  unfold os_sched_lock_call_relation; split; [|reflexivity].
  destruct before.(SchedState).(isRunning); [constructor|reflexivity].
Qed.

Lemma os_sched_lock_call_preserves_validity : forall critical sg invocation before entry final,
  UCOS2_state_inv sg before ->
  os_sched_lock_call_relation critical sg invocation before entry final ->
  UCOS2_state_inv sg final.
Proof.
  intros critical sg invocation before entry final Hvalid [Hinterval ->].
  apply os_sched_lock_checkpoint_preserves_validity.
  destruct before.(SchedState).(isRunning).
  - exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)).
  - subst entry; exact Hvalid.
Qed.

Lemma os_sched_lock_acquire_facts : forall critical sg invocation mask saved before entry,
  UCOS2_state_inv sg before -> os_sched_lock_running before = 1 ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  os_sched_lock_body_facts critical sg invocation mask saved before entry.
Proof.
  intros critical sg invocation mask saved before entry Hvalid Hrunning Hinterval Hsaved.
  unfold os_sched_lock_running in Hrunning.
  destruct before.(SchedState).(isRunning) eqn:Hrun; [|discriminate].
  unfold os_sched_lock_body_facts.
  split; [exact Hrun|]. split; [exact Hinterval|]. split; [|exact Hsaved].
  exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)).
Qed.

Lemma os_sched_lock_save_consequence : forall critical sg invocation mask saved before entry,
  UCOS2_state_inv sg before -> os_sched_lock_running before = 1 ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  UCOS2_raw_rep sg entry |--
    coq_prop (os_sched_lock_body_facts critical sg invocation mask saved before entry) &&
    UCOS2_inv sg entry.
Proof.
  intros critical sg invocation mask saved before entry Hvalid Hrunning Hinterval Hsaved.
  pose proof (os_sched_lock_acquire_facts critical sg invocation mask saved before entry
    Hvalid Hrunning Hinterval Hsaved) as Hfacts.
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid))
    as Hentry.
  unfold UCOS2_inv; entailer!.
Qed.

Lemma os_sched_lock_split_counters : forall sg entry,
  UCOS2_inv sg entry |--
    coq_prop (UCOS2_state_inv sg entry /\
      0 <= os_sched_lock_locks entry <= 255) &&
    (sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints entry **
     sg.(g_OSLockNesting) # UChar |-> os_sched_lock_locks entry **
     UCOS2_raw_rep_missing_interrupt sg entry).
Proof.
  intros; rewrite UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, os_sched_lock_ints, os_sched_lock_locks.
  Intros.
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) entry.(IntrState).(lockNesting)).
  entailer!.
Qed.

Lemma os_sched_lock_merge_counters : forall sg entry,
  UCOS2_state_inv sg entry ->
  sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints entry **
  sg.(g_OSLockNesting) # UChar |-> os_sched_lock_updated_locks entry **
  UCOS2_raw_rep_missing_interrupt sg entry |--
    UCOS2_inv sg (os_sched_lock_checkpoint true entry).
Proof.
  intros sg entry Hvalid.
  pose proof (os_sched_lock_checkpoint_ints_eq true entry) as Hints.
  unfold os_sched_lock_ints, os_sched_lock_checkpoint in Hints; simpl in Hints.
  rewrite <- Hints at 1.
  exact (os_sched_lock_merge_inv sg true entry Hvalid).
Qed.

Lemma os_sched_lock_restore_consequence : forall platform critical sg invocation origin mask saved before entry,
  os_sched_lock_body_facts critical sg invocation mask saved before entry ->
  sg.(g_OSRunning) # UChar |-> os_sched_lock_running (os_sched_lock_checkpoint true entry) **
  os_sched_lock_outside_frame platform critical sg invocation origin mask
    (os_sched_lock_checkpoint true entry) |--
  os_sched_lock_post platform critical sg invocation origin mask before.
Proof.
  intros platform critical sg invocation origin mask saved before entry
    [Hrun [Hinterval [Hvalid Hsaved]]].
  unfold os_sched_lock_post; Exists entry (os_sched_lock_checkpoint true entry).
  assert (Hfinal : UCOS2_state_inv sg (os_sched_lock_checkpoint true entry)).
  { apply os_sched_lock_checkpoint_preserves_validity; exact Hvalid. }
  unfold os_sched_lock_call_relation; rewrite Hrun; entailer!.
Qed.

Lemma os_sched_lock_not_running_return : forall platform critical sg invocation origin mask before,
  UCOS2_state_inv sg before -> os_sched_lock_running before <> 1 ->
  sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
  os_sched_lock_outside_frame platform critical sg invocation origin mask before |--
  os_sched_lock_post platform critical sg invocation origin mask before.
Proof.
  intros platform critical sg invocation origin mask before Hvalid Hnotrunning.
  unfold os_sched_lock_running in Hnotrunning.
  destruct before.(SchedState).(isRunning) eqn:Hrun; [contradiction|].
  unfold os_sched_lock_post; Exists before before.
  pose proof (proj1 (os_sched_lock_not_running_no_effect before)) as Hidentity.
  unfold os_sched_lock_call_relation; rewrite Hrun, Hidentity; entailer!.
Qed.
