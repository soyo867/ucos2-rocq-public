Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.

Import UCOS2_C_Rules ListNotations EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected V2.93.01 names/IEC-disabled OSSemCreate source order:
    observe OSIntNesting; Save; observe/pop the CURRENT ECB free list;
    Restore; initialize the detached ECB; return/publish the handle.
    These are model/call-composition interfaces, not a completed C proof.
    In particular the allocation snapshot is NOT the pre-Save snapshot. *)
Definition sem_create_int_nesting (state : UCOS2_Verify_State) : Z :=
  state.(IntrState).(intNesting).

(** Reuse the existing CPU/CSL representation contract, without adding a
    second independently acquirable handle. This equation does not prove
    ARM code or authorize arbitrary unmasked shared-memory access. *)
Lemma sem_create_closed_region_equiv : forall critical sg invocation state,
  critical_region_outside critical sg invocation state --||--
    UCOS2_raw_rep sg state.
Proof.
  intros; unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  symmetry; apply UCOS2_raw_rep_split_running.
Qed.


Definition sem_create_observation_frame (platform : InterruptPlatformResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (mask : Z) (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin mask **
  interrupt_inv_no_int_nesting sg state.(IntrState) **
  UCOS2_raw_rep_missing_interrupt sg state.

Definition sem_create_pre (platform : InterruptPlatformResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (mask : Z) (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg before) &&
    (sg.(g_OSIntNesting) # UChar |-> sem_create_int_nesting before **
     sem_create_observation_frame platform sg invocation origin mask before).

Lemma sem_create_pre_closed_equiv : forall platform critical sg invocation origin mask before,
  sem_create_pre platform sg invocation origin mask before --||--
    coq_prop (UCOS2_state_inv sg before) &&
      (interrupt_platform_running platform invocation origin mask **
       critical_region_outside critical sg invocation before).
Proof.
  intros; rewrite sem_create_closed_region_equiv.
  rewrite (UCOS2_raw_rep_split_module sg before InterruptModule).
  cbn [UCOS2_module_rep].
  unfold sem_create_pre, sem_create_observation_frame, sem_create_int_nesting,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  split; entailer!.
Qed.

(** A Restore may allow foreign registered actions between ANY two private
    stores, including between WaitListInit's writes and before publication.
    The Event invocation identifies the allocation being framed; it does
    not manufacture its bytes. The same physical private storage is held
    separately, as in event_create_private_store_merge. *)
Fixpoint sem_create_private_stores_interleaved
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (task_invocation event_invocation : nat) (eid : EventID)
  (writes : list (EventField * Z)) : program UCOS2_Verify_State unit :=
  match writes with
  | [] => fun before result after => result = tt /\
      critical_region_event_interval critical sg task_invocation event_invocation before after
  | (field, stored) :: rest => fun before result after => exists entry allocation,
      critical_region_event_interval critical sg task_invocation event_invocation before entry /\
      entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateInvocation) = event_invocation /\
      sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid rest
        (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some stored)) entry)
        result after
  end.

Lemma sem_create_private_stores_interleaved_post :
  forall critical sg task_invocation event_invocation eid writes before result after allocation,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid writes
    before result after ->
  UCOS2_state_inv sg after /\ exists final,
    after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
    final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
    final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
    final.(eventPrivateStorage) = event_create_stores_image allocation.(eventPrivateStorage) writes.
Proof.
  intros critical sg task_invocation event_invocation eid writes.
  induction writes as [|[field stored] rest IH];
    intros before result after allocation Hvalid Hget Hinv Hsteps.
  - destruct Hsteps as [_ Htrace].
    pose proof (proj1 (critical_region_event_interval_transports_resources
      _ _ _ _ _ _ Htrace Hvalid)) as Hafter.
    destruct (event_create_environment_preserves_allocation
      _ _ _ _ _ _ _ _ Htrace Hvalid Hget Hinv) as [Hlookup _].
    split; [exact Hafter|]; exists allocation; repeat split; assumption || reflexivity.
  - destruct Hsteps as [entry [current [Htrace [Hcurrent [Hcurrent_inv Htail]]]]].
    pose proof (proj1 (critical_region_event_interval_transports_resources
      _ _ _ _ _ _ Htrace Hvalid)) as Hentry.
    destruct (event_create_environment_preserves_allocation
      _ _ _ _ _ _ _ _ Htrace Hvalid Hget Hinv) as [Hlookup _].
    assert (current = allocation) by congruence; subst current.
    eapply (IH
      (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some stored)) entry)
      result after
      {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
         eventPrivateGeneration := allocation.(eventPrivateGeneration);
         eventPrivateQueue := allocation.(eventPrivateQueue);
         eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
         eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |});
      [|apply kernel_map_set_same|exact Hinv|exact Htail].
    eapply UCOS2_event_private_write_preserves_validity; eassumption.
Qed.

Lemma sem_create_private_stores_without_interference :
  forall critical sg task_invocation eid writes before result after allocation,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_create_private_stores eid writes before result after ->
  sem_create_private_stores_interleaved critical sg task_invocation
    allocation.(eventPrivateInvocation) eid writes before result after.
Proof.
  intros critical sg task_invocation eid writes; induction writes as [|[field stored] rest IH];
    intros before result after allocation Hget Hsteps.
  - destruct Hsteps as [-> ->]; split; [reflexivity|constructor].
  - destruct Hsteps as [current [Hcurrent Htail]].
    assert (current = allocation) by congruence; subst current.
    exists before, allocation; split; [constructor|].
    split; [exact Hget|]; split; [reflexivity|].
    eapply (IH _ result after
      {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
         eventPrivateGeneration := allocation.(eventPrivateGeneration);
         eventPrivateQueue := allocation.(eventPrivateQueue);
         eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
         eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |});
      [apply kernel_map_set_same|exact Htail].
Qed.

Lemma sem_create_private_stores_interleaved_mutex_pcp_eq :
  forall critical sg task_invocation event_invocation eid writes before result after allocation final,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid writes
    before result after ->
  after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  final.(eventPrivateMutexPCP) = allocation.(eventPrivateMutexPCP).
Proof.
  intros critical sg task_invocation event_invocation eid writes.
  induction writes as [|[field stored] rest IH];
    intros before result after allocation final Hvalid Hget Hinv Hsteps Hfinal.
  - destruct Hsteps as [_ Htrace].
    destruct (event_create_environment_preserves_allocation
      _ _ _ _ _ _ _ _ Htrace Hvalid Hget Hinv) as [Hlookup _].
    assert (final = allocation) by congruence; subst final; reflexivity.
  - destruct Hsteps as [entry [current [Htrace [Hcurrent [Hcurrent_inv Htail]]]]].
    pose proof (proj1 (critical_region_event_interval_transports_resources
      _ _ _ _ _ _ Htrace Hvalid)) as Hentry.
    destruct (event_create_environment_preserves_allocation
      _ _ _ _ _ _ _ _ Htrace Hvalid Hget Hinv) as [Hlookup _].
    assert (current = allocation) by congruence; subst current.
    eapply (IH
      (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some stored)) entry)
      result after
      {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
         eventPrivateGeneration := allocation.(eventPrivateGeneration);
         eventPrivateQueue := allocation.(eventPrivateQueue);
         eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
         eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |}
      final); [|apply kernel_map_set_same|exact Hinv|exact Htail|exact Hfinal].
    eapply UCOS2_event_private_write_preserves_validity; eassumption.
Qed.

(** Historical names-disabled call binding.  Its initialized image is
    still the old source projection; the configured publication library
    above must not silently turn this into a proof of the names-enabled
    C call.  The latter also needs the source literal's lifetime protocol. *)
Definition sem_create_call_relation (critical : CriticalRegionResources)
  (sg : StableGlobVars) (task_invocation : nat) (count : Z)
  (before : UCOS2_Verify_State) (result : addr) (after : UCOS2_Verify_State) : Prop :=
  if event_create_isr_rejected (sem_create_int_nesting before)
  then result = 0 /\ after = before
  else exists entry allocated allocation_result,
    critical_region_interval critical sg task_invocation before entry /\
    event_create_allocate_critical entry allocation_result allocated /\
    match allocation_result with
    | None => result = 0 /\
        critical_region_interval critical sg task_invocation allocated after
    | Some (eid, image) => exists initialized allocation,
        sem_create_private_stores_interleaved critical sg task_invocation
          entry.(EventState).(eventLifecycle).(eventNextInvocation) eid
          (event_create_initialization_fields false 3 count 0 0) allocated tt initialized /\
        initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        result = event_pool_addr sg eid /\
        after = replace_EventS
          (event_publish initialized.(EventState) eid (sem_create_event allocation count 0)) initialized
    end.

(** No post-validity test is hidden in the source relation. ISR rejection
    and exhaustion are genuine branches; arbitrary certified environment
    changes are retained, including after the empty-pool Restore. *)
Lemma sem_create_call_preserves_validity : forall critical sg invocation count before result after,
  UCOS2_state_inv sg before -> 0 <= count <= 65535 ->
  sem_create_call_relation critical sg invocation count before result after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation count before result after Hvalid Hcount Hcall.
  unfold sem_create_call_relation in Hcall.
  destruct (event_create_isr_rejected (sem_create_int_nesting before)).
  - destruct Hcall as [_ ->]; exact Hvalid.
  - destruct Hcall as [entry [allocated [allocation_result [Hentry_trace [Hallocate Hreturn]]]]].
    pose proof (proj1 (critical_region_interval_transports_resources
      _ _ _ _ _ Hentry_trace Hvalid)) as Hentry.
    pose proof (event_create_allocate_critical_preserves_validity
      sg entry allocation_result allocated Hentry Hallocate) as Hallocated.
    destruct allocation_result as [[eid image]|].
    + destruct Hreturn as [initialized [allocation [Hstores [Hget [_ ->]]]]].
      pose proof (proj2 (event_create_allocate_critical_private_result
        entry eid image allocated Hallocate)) as Hprivate.
      destruct (sem_create_private_stores_interleaved_post
        _ _ _ _ _ _ _ _ _ _ Hallocated Hprivate eq_refl Hstores) as [Hinitialized _].
      pose proof (sem_create_private_stores_interleaved_mutex_pcp_eq
        _ _ _ _ _ _ _ _ _ _ _ Hallocated Hprivate eq_refl Hstores Hget) as HnoMutexLease.
      eapply sem_create_publish_preserves_validity; try eassumption.
      apply event_name_valid_disabled.
      pose proof Hinitialized as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto.
    + destruct Hreturn as [_ Hreturn_trace].
      exact (proj1 (critical_region_interval_transports_resources
        _ _ _ _ _ Hreturn_trace Hallocated)).
Qed.

Lemma sem_create_call_exists : forall critical sg invocation count before,
  UCOS2_state_inv sg before ->
  exists result after, sem_create_call_relation critical sg invocation count before result after.
Proof.
  intros critical sg invocation count before Hvalid.
  unfold sem_create_call_relation.
  destruct (event_create_isr_rejected (sem_create_int_nesting before)).
  - exists 0, before; split; reflexivity.
  - destruct (event_create_allocate_critical_exists sg before Hvalid)
      as [allocation_result [allocated Hallocate]].
    destruct allocation_result as [[eid image]|].
    + pose proof (proj2 (event_create_allocate_critical_private_result
        before eid image allocated Hallocate)) as Hprivate.
      destruct (event_create_private_stores_exists eid
        (event_create_initialization_fields false 3 count 0 0) allocated _ Hprivate)
        as [initialized Hstores].
      destruct (event_create_private_stores_post_allocation eid _ allocated tt initialized
        _ Hprivate Hstores) as [allocation [Hget Himage]].
      exists (event_pool_addr sg eid),
        (replace_EventS (event_publish initialized.(EventState) eid
          (sem_create_event allocation count 0)) initialized).
      exists before, allocated, (Some (eid, image)); split; [constructor|].
      split; [exact Hallocate|]; exists initialized, allocation; split.
      * exact (sem_create_private_stores_without_interference critical sg invocation
          eid _ allocated tt initialized _ Hprivate Hstores).
      * split; [exact Hget|]; split; reflexivity.
    + exists 0, allocated; exists before, allocated, None.
      split; [constructor|]; split; [exact Hallocate|]; split; [reflexivity|constructor].
Qed.

(** The initialized image is derived from the actual stores and allocation
    frame, NOT assumed of an arbitrary published node. The left side owns
    the real completed ECB plus current shared resources. Invocation and
    generation equalities alone cannot discharge this spatial obligation. *)
Lemma sem_create_interleaved_publish_merge :
  forall critical sg task_invocation event_invocation eid before initialized allocation final count,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  allocation.(eventPrivateQueue) = None ->
  0 <= count <= 65535 ->
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid
    (event_create_initialization_fields false 3 count 0 0) before tt initialized ->
  initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  allocation.(eventPrivateMutexPCP) = None ->
  event_private_storage_rep sg eid final **
    (event_raw_rep sg initialized.(TskState) initialized.(EventState) **
     queue_storage_rep sg initialized.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg initialized) |--
  UCOS2_inv sg
    (replace_EventS (event_publish initialized.(EventState) eid (sem_create_event final count 0)) initialized).
Proof.
  intros critical sg task_invocation event_invocation eid before initialized allocation final count
    Hvalid Hget Hinv Hqueue Hcount Hstores Hfinal HnoMutexLease.
  destruct (sem_create_private_stores_interleaved_post
    _ _ _ _ _ _ _ _ _ _ Hvalid Hget Hinv Hstores)
    as [Hinitialized [current [Hcurrent [_ [_ [Hqueue_after Himage]]]]]].
  assert (current = final) by congruence; subst current.
  rewrite event_create_stores_image_initialization_eq in Himage.
  assert (Hdisabled : sg.(osKernelConfig).(cfgEventNames) = false).
  { pose proof Hinitialized as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  pose proof (sem_create_private_stores_interleaved_mutex_pcp_eq
    _ _ _ _ _ _ _ _ _ _ _ Hvalid Hget Hinv Hstores Hfinal) as HleaseEq.
  eapply sem_create_publish_merge; [exact Hinitialized|exact Hfinal|
    rewrite Hqueue_after; exact Hqueue| |exact Hcount| |].
  - rewrite Hdisabled; exact Himage.
  - apply event_name_valid_disabled; exact Hdisabled.
  - rewrite HleaseEq; exact HnoMutexLease.
Qed.

Definition sem_create_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask count : Z)
  (before : UCOS2_Verify_State) (result : addr) : Assertion :=
  EX after, coq_prop
    (sem_create_call_relation critical sg invocation count before result after /\
     UCOS2_state_inv sg after) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation after).

(** Closing the call needs the actual returned execution resource and
    current closed region. This consequence does not implement Restore
    or turn a saved numeric word into a platform resource. *)
Lemma sem_create_call_close : forall platform critical sg invocation origin mask count before result after,
  UCOS2_state_inv sg before -> 0 <= count <= 65535 ->
  sem_create_call_relation critical sg invocation count before result after ->
  interrupt_platform_running platform invocation origin mask **
    critical_region_outside critical sg invocation after |--
  sem_create_post platform critical sg invocation origin mask count before result.
Proof.
  intros platform critical sg invocation origin mask count before result after Hvalid Hcount Hcall.
  pose proof (sem_create_call_preserves_validity _ _ _ _ _ _ _ Hvalid Hcount Hcall) as Hafter.
  unfold sem_create_post; Exists after; entailer!.
Qed.

Lemma sem_create_isr_return : forall platform critical sg invocation origin mask count before,
  0 < sem_create_int_nesting before ->
  sem_create_pre platform sg invocation origin mask before |--
    sem_create_post platform critical sg invocation origin mask count before 0.
Proof.
  intros platform critical sg invocation origin mask count before Hnesting.
  rewrite (sem_create_pre_closed_equiv platform critical sg invocation origin mask before).
  Intros; unfold sem_create_post; Exists before.
  assert (Hbranch : event_create_isr_rejected (sem_create_int_nesting before) = true).
  { apply Z.ltb_lt; exact Hnesting. }
  assert (Hcall : sem_create_call_relation critical sg invocation count before 0 before).
  { unfold sem_create_call_relation; rewrite Hbranch; split; reflexivity. }
  entailer!.
Qed.

(** An observation loan is a decomposition of the same region, never an
    extra cell that can be framed across ordinary acquisition. *)
Lemma sem_create_closed_region_excludes_int_nesting_loan :
  forall critical sg invocation state observed,
  sg.(g_OSIntNesting) # UChar |-> observed **
    critical_region_outside critical sg invocation state |-- coq_prop False.
Proof.
  intros; rewrite sem_create_closed_region_equiv.
  rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state, store_uchar; pureIntros.
  sep_apply_l_atomic (dup_store_byte sg.(g_OSIntNesting) observed state.(IntrState).(intNesting)).
  entailer!.
Qed.

(** The public observation is the returned pointer of the ordered source
    relation, not the historical entry-snapshot atomic shortcut. *)
Definition sem_create_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (count : Z)
  : program UCOS2_Verify_State Z := sem_create_call_relation critical sg invocation count.

Definition sem_create_observe_pointer (pointer : Z) : program (UCOS2_Verify_State -> Prop) Z :=
  StateRelMonad.ret pointer.

Lemma sem_create_safe_return : forall (c : program UCOS2_Verify_State Z) before after pointer X,
  c before pointer after ->
  safeExec (LastSeen before) (bind (atomic_cmd c) sem_create_observe_pointer) X ->
  safeExec (LastSeen after) (StateRelMonad.ret pointer) X.
Proof.
  intros c before after pointer X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd c) (LastSeen before) (LastSeen after) pointer).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P0 HP0.
    exists (RTrans_Abs after); split.
    - exists before, after; split; [apply HP0; exact I|].
      split; [exact Hsem|intro state; split; trivial].
    - intro state; split; trivial. }
  exact (highstepbind_derive _ _ _ pointer (LastSeen after) Hatomic X Hexec).
Qed.

Lemma sem_create_pre_running_inv_equiv : forall platform (critical : CriticalRegionResources) sg invocation origin mask current,
  sem_create_pre platform sg invocation origin mask current --||--
    (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg current).
Proof.
  intros; rewrite (sem_create_pre_closed_equiv platform critical sg invocation origin mask current),
    sem_create_closed_region_equiv; unfold UCOS2_inv; split; entailer!.
Qed.

Definition sem_create_acquire_facts (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (mask saved : Z) (before entry : UCOS2_Verify_State) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved.

Lemma sem_create_acquire_consequence : forall critical sg invocation mask saved before entry,
  UCOS2_state_inv sg before -> critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved -> UCOS2_raw_rep sg entry |--
    coq_prop (sem_create_acquire_facts critical sg invocation mask saved before entry) && UCOS2_inv sg entry.
Proof.
  intros critical sg invocation mask saved before entry Hvalid Hinterval Hsaved.
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)) as Hentry.
  unfold sem_create_acquire_facts, UCOS2_inv; entailer!.
Qed.

Lemma sem_create_event_interval_trans : forall critical sg invocation event_invocation first middle last,
  critical_region_event_interval critical sg invocation event_invocation first middle ->
  critical_region_event_interval critical sg invocation event_invocation middle last ->
  critical_region_event_interval critical sg invocation event_invocation first last.
Proof.
  intros critical sg invocation event_invocation first middle last Hfirst Hlast.
  eapply KernelResumptionTraceSegment with (stopped1 := false) (stopped2 := false).
  - eapply kernel_resumption_resource_trace_erases; exact Hfirst.
  - eapply kernel_resumption_resource_trace_timer_projection; exact Hfirst.
  - exact Hlast.
Qed.

Lemma sem_create_private_prefix_environment :
  forall critical sg invocation event_invocation eid writes initial current after,
  sem_create_private_stores_interleaved critical sg invocation event_invocation eid writes initial tt current ->
  critical_region_event_interval critical sg invocation event_invocation current after ->
  sem_create_private_stores_interleaved critical sg invocation event_invocation eid writes initial tt after.
Proof.
  intros critical sg invocation event_invocation eid writes.
  induction writes as [|[field value] rest IH]; intros initial current after Hstores Hinterval.
  - destruct Hstores as [_ Hfirst]; split; [reflexivity|eapply sem_create_event_interval_trans; eassumption].
  - destruct Hstores as [entry [allocation [Hentry [Hget [Hinv Htail]]]]].
    exists entry, allocation; split; [exact Hentry|]; split; [exact Hget|].
    split; [exact Hinv|]; eapply IH; eassumption.
Qed.

Lemma sem_create_private_prefix_append :
  forall critical sg invocation event_invocation eid writes initial current allocation field stored,
  sem_create_private_stores_interleaved critical sg invocation event_invocation eid writes initial tt current ->
  current.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  sem_create_private_stores_interleaved critical sg invocation event_invocation eid
    (writes ++ [(field, stored)]) initial tt
    (replace_EventS (event_private_write current.(EventState) eid allocation field (Some stored)) current).
Proof.
  intros critical sg invocation event_invocation eid writes.
  induction writes as [|[head_field head_value] rest IH];
    intros initial current allocation field stored Hstores Hget Hinv.
  - destruct Hstores as [_ Hinterval]; exists current, allocation.
    split; [exact Hinterval|]. split; [exact Hget|]. split; [exact Hinv|].
    split; [reflexivity|constructor].
  - destruct Hstores as [entry [head_allocation [Hentry [Hhead [Hhead_inv Htail]]]]].
    exists entry, head_allocation; split; [exact Hentry|]. split; [exact Hhead|].
    split; [exact Hhead_inv|]; eapply IH; eassumption.
Qed.

(** A current-state prefix context, separate from the real private ECB.
    Its environment transport below requires the actual resumed raw heap.
    It is not ordinary-frame stability or a source/CPU/CSL embedding. *)
Definition sem_create_private_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (eid : EventID)
  (initial : UCOS2_Verify_State) (allocation : EventPrivateAllocation)
  (writes : list (EventField * Z)) : Assertion :=
  EX current,
    coq_prop (sem_create_private_stores_interleaved critical sg invocation
      allocation.(eventPrivateInvocation) eid writes initial tt current) &&
    sem_create_pre platform sg invocation origin mask current.

Lemma sem_create_private_context_begin : forall platform critical sg invocation origin mask eid initial allocation,
  sem_create_pre platform sg invocation origin mask initial |--
  sem_create_private_context platform critical sg invocation origin mask eid initial allocation [].
Proof.
  intros; unfold sem_create_private_context; Exists initial.
  assert (Hnil : sem_create_private_stores_interleaved critical sg invocation
    allocation.(eventPrivateInvocation) eid [] initial tt initial)
    by (split; [reflexivity|constructor]).
  entailer!.
Qed.

Lemma sem_create_private_context_after_environment :
  forall platform critical sg invocation origin mask eid initial allocation writes current after,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  sem_create_private_stores_interleaved critical sg invocation
    allocation.(eventPrivateInvocation) eid writes initial tt current ->
  critical_region_event_interval critical sg invocation allocation.(eventPrivateInvocation) current after ->
  interrupt_platform_running platform invocation origin mask ** UCOS2_raw_rep sg after |--
  sem_create_private_context platform critical sg invocation origin mask eid initial allocation writes.
Proof.
  intros platform critical sg invocation origin mask eid initial allocation writes current after
    Hvalid Hget Hprefix Hinterval.
  pose proof (sem_create_private_prefix_environment _ _ _ _ _ _ _ _ _ Hprefix Hinterval) as Hafter.
  pose proof (proj1 (sem_create_private_stores_interleaved_post
    _ _ _ _ _ _ _ _ _ _ Hvalid Hget eq_refl Hafter)) as Hvalid_after.
  unfold sem_create_private_context; Exists after.
  rewrite (sem_create_pre_running_inv_equiv platform critical sg invocation origin mask after).
  unfold UCOS2_inv; entailer!.
Qed.

Lemma sem_create_private_context_open :
  forall platform critical sg invocation origin mask eid initial allocation writes,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  sem_create_private_context platform critical sg invocation origin mask eid initial allocation writes |--
  EX current final,
    coq_prop (sem_create_private_stores_interleaved critical sg invocation
      allocation.(eventPrivateInvocation) eid writes initial tt current /\
      current.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
      final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
      final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
      final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
      final.(eventPrivateMutexPCP) = allocation.(eventPrivateMutexPCP) /\
      final.(eventPrivateStorage) = event_create_stores_image allocation.(eventPrivateStorage) writes) &&
    (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg current).
Proof.
  intros platform critical sg invocation origin mask eid initial allocation writes Hvalid Hget.
  unfold sem_create_private_context; Intros current.
  match goal with H : sem_create_private_stores_interleaved _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hprefix end.
  destruct (sem_create_private_stores_interleaved_post _ _ _ _ _ _ _ _ _ _ Hvalid Hget eq_refl Hprefix)
    as [Hcurrent [final [Hfinal [Hinv [Hgen [Hqueue Himage]]]]]].
  pose proof (sem_create_private_stores_interleaved_mutex_pcp_eq
    _ _ _ _ _ _ _ _ _ _ _ Hvalid Hget eq_refl Hprefix Hfinal) as Hpcp.
  Exists current final.
  rewrite (sem_create_pre_running_inv_equiv platform critical sg invocation origin mask current); entailer!.
Qed.

Lemma sem_create_private_context_merge_field :
  forall platform critical sg invocation origin mask eid initial allocation writes field stored,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_cell (event_pool_addr sg eid) field (Some stored) **
    sem_create_private_context platform critical sg invocation origin mask eid initial allocation writes |--
  event_cell (event_pool_addr sg eid) field (Some stored) **
    sem_create_private_context platform critical sg invocation origin mask eid initial allocation
      (writes ++ [(field, stored)]).
Proof.
  intros platform critical sg invocation origin mask eid initial allocation writes field stored Hvalid Hget.
  sep_apply_l_atomic (sem_create_private_context_open platform critical sg invocation origin mask
    eid initial allocation writes Hvalid Hget).
  Intros current final.
  match goal with H : _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ |- _ =>
    destruct H as [Hprefix [Hfinal [Hinv [Hgen [Hqueue [Hpcp Himage]]]]]] end.
  sep_apply_l_atomic (UCOS2_event_private_write_global_frame sg current eid final field (Some stored) Hfinal).
  unfold sem_create_private_context; Exists
    (replace_EventS (event_private_write current.(EventState) eid final field (Some stored)) current).
  assert (Hafter : sem_create_private_stores_interleaved critical sg invocation
    allocation.(eventPrivateInvocation) eid (writes ++ [(field, stored)]) initial tt
    (replace_EventS (event_private_write current.(EventState) eid final field (Some stored)) current)).
  { eapply sem_create_private_prefix_append; eassumption. }
  rewrite (sem_create_pre_running_inv_equiv platform critical sg invocation origin mask _); entailer!.
Qed.

Lemma sem_create_private_prefix_append_stores :
  forall critical sg invocation event_invocation eid additional writes initial current after allocation,
  sem_create_private_stores_interleaved critical sg invocation event_invocation eid writes initial tt current ->
  current.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  event_create_private_stores eid additional current tt after ->
  sem_create_private_stores_interleaved critical sg invocation event_invocation eid
    (writes ++ additional) initial tt after.
Proof.
  intros critical sg invocation event_invocation eid additional.
  induction additional as [|[field value] rest IH]; intros writes initial current after allocation Hprefix Hget Hinv Htail.
  - destruct Htail as [_ ->]; rewrite app_nil_r; exact Hprefix.
  - destruct Htail as [actual [Hactual Htail]].
    assert (actual = allocation) by congruence; subst actual.
    replace (writes ++ (field, value) :: rest) with ((writes ++ [(field, value)]) ++ rest)
      by (rewrite <- app_assoc; reflexivity).
    eapply (IH _ _ _ _
      {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
         eventPrivateGeneration := allocation.(eventPrivateGeneration);
         eventPrivateQueue := allocation.(eventPrivateQueue);
         eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
         eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some value) |}).
    + eapply sem_create_private_prefix_append; eassumption.
    + apply kernel_map_set_same.
    + exact Hinv.
    + exact Htail.
Qed.

Lemma sem_create_private_stores_global_frame : forall sg eid writes initial result after,
  event_create_private_stores eid writes initial result after ->
  UCOS2_inv sg initial |-- UCOS2_inv sg after.
Proof.
  intros sg eid writes; induction writes as [|[field value] rest IH]; intros initial result after Hstores.
  - destruct Hstores as [_ ->]; reflexivity.
  - destruct Hstores as [allocation [Hget Htail]].
    eapply derivable1_trans.
    + apply (UCOS2_event_private_write_global_frame sg initial eid allocation field (Some value) Hget).
    + eapply IH; exact Htail.
Qed.

Definition sem_create_wait_list_stores : list (EventField * Z) :=
  [(EventGrpField, 0)] ++ map (fun row => (event_table_field (Z.of_nat row), 0)) (seq 0 8).

Lemma sem_create_private_context_merge_wait_list :
  forall platform critical sg invocation origin mask eid initial allocation writes,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    sem_create_private_context platform critical sg invocation origin mask eid initial allocation writes |--
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    sem_create_private_context platform critical sg invocation origin mask eid initial allocation
      (writes ++ sem_create_wait_list_stores).
Proof.
  intros platform critical sg invocation origin mask eid initial allocation writes Hvalid Hget.
  sep_apply_l_atomic (sem_create_private_context_open platform critical sg invocation origin mask
    eid initial allocation writes Hvalid Hget).
  Intros current final.
  match goal with H : _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ |- _ =>
    destruct H as [Hprefix [Hfinal [Hinv [Hgen [Hqueue [Hpcp Himage]]]]]] end.
  destruct (event_create_private_stores_exists eid sem_create_wait_list_stores current final Hfinal)
    as [after Htail].
  sep_apply_l_atomic (sem_create_private_stores_global_frame sg eid sem_create_wait_list_stores current tt after Htail).
  unfold sem_create_private_context; Exists after.
  assert (Hafter : sem_create_private_stores_interleaved critical sg invocation
    allocation.(eventPrivateInvocation) eid (writes ++ sem_create_wait_list_stores) initial tt after).
  { eapply sem_create_private_prefix_append_stores; eassumption. }
  rewrite (sem_create_pre_running_inv_equiv platform critical sg invocation origin mask after); entailer!.
Qed.

(** This is the existing allocation record returned by event_detach_head,
    not a new ghost resource or an alternative ECB owner. *)
Definition sem_create_allocation_identity (entry : UCOS2_Verify_State) (image : EventStorage)
  : EventPrivateAllocation :=
  {| eventPrivateInvocation := entry.(EventState).(eventLifecycle).(eventNextInvocation);
     eventPrivateGeneration := entry.(EventState).(eventLifecycle).(eventNextGeneration);
     eventPrivateQueue := None; eventPrivateMutexPCP := None; eventPrivateStorage := image |}.

Lemma sem_create_private_context_publish :
  forall platform critical sg invocation origin mask before entry allocated eid image count,
  critical_region_interval critical sg invocation before entry ->
  sem_create_int_nesting before <= 0 -> UCOS2_state_inv sg entry -> 0 <= count <= 65535 ->
  event_create_allocate_critical entry (Some (eid, image)) allocated ->
  event_storage_rep false (event_pool_addr sg eid) (event_create_image false 3 count 0 0 image) **
    sem_create_private_context platform critical sg invocation origin mask eid allocated
      (sem_create_allocation_identity entry image)
      (event_create_initialization_fields false 3 count 0 0) |--
  EX after, coq_prop (sem_create_call_relation critical sg invocation count before (event_pool_addr sg eid) after) &&
    sem_create_pre platform sg invocation origin mask after.
Proof.
  intros platform critical sg invocation origin mask before entry allocated eid image count
    Hentry Hnesting Hvalid Hcount Hallocate.
  pose proof (event_create_allocate_critical_preserves_validity sg entry _ allocated Hvalid Hallocate) as Hallocated.
  pose proof (proj2 (event_create_allocate_critical_private_result entry eid image allocated Hallocate)) as Hget.
  change (allocated.(EventState).(eventLifecycle).(eventPrivate) eid =
    Some (sem_create_allocation_identity entry image)) in Hget.
  sep_apply_l_atomic (sem_create_private_context_open platform critical sg invocation origin mask eid allocated
    (sem_create_allocation_identity entry image)
    (event_create_initialization_fields false 3 count 0 0) Hallocated Hget).
  Intros current final.
  match goal with H : _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ |- _ =>
    destruct H as [Hprefix [Hfinal [Hinv [Hgen [Hqueue [Hpcp Himage]]]]]] end.
  pose proof (proj1 (sem_create_private_stores_interleaved_post
    _ _ _ _ _ _ _ _ _ _ Hallocated Hget eq_refl Hprefix)) as Hcurrent.
  rewrite event_create_stores_image_initialization_eq in Himage.
  cbn [sem_create_allocation_identity eventPrivateStorage eventPrivateQueue eventPrivateMutexPCP] in Himage, Hqueue, Hpcp.
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false).
  { destruct Hcurrent as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hstorage : event_storage_rep false (event_pool_addr sg eid)
    (event_create_image false 3 count 0 0 image) |-- event_private_storage_rep sg eid final).
  { unfold event_private_storage_rep; rewrite Hnames, Himage; reflexivity. }
  set (published := replace_EventS (event_publish current.(EventState) eid (sem_create_event final count 0)) current).
  assert (Hcall : sem_create_call_relation critical sg invocation count before (event_pool_addr sg eid) published).
  { unfold sem_create_call_relation.
    assert (Hnotisr : event_create_isr_rejected (sem_create_int_nesting before) = false)
      by (apply Z.ltb_ge; exact Hnesting).
    rewrite Hnotisr; exists entry, allocated, (Some (eid, image)).
    split; [exact Hentry|]; split; [exact Hallocate|].
    exists current, final; split; [exact Hprefix|]. split; [exact Hfinal|]. split; reflexivity. }
  sep_apply_l_atomic Hstorage.
  rewrite (UCOS2_inv_split_event_queue sg current); Intros.
  Exists published.
  rewrite (sem_create_pre_running_inv_equiv platform critical sg invocation origin mask published).
  eapply derivable1_trans with (y := interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg published).
  2: { entailer!. }
  unfold published.
  eapply derivable1_trans.
  2: { apply derivable1_sepcon_mono; [reflexivity|].
    eapply sem_create_interleaved_publish_merge;
      [exact Hallocated|exact Hget|reflexivity|reflexivity|exact Hcount|exact Hprefix|exact Hfinal|reflexivity]. }
  entailer!.
Qed.
