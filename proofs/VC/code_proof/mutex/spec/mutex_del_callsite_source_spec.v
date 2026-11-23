Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_recheck_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition mutex_del_callsite_environment environment external platform : Prop :=
  environment.(mutex_del_call_external) = external /\
  environment.(mutex_del_call_platform) = platform.

(** The earlier dynamic-only Require omitted the actual caller's table,
    execution context and whole parked map. This entry owns those present
    resources; it is not equivalent to the old Require by itself. No future
    Save/Restore outcome, owner protocol or scheduler premise is included.
    ISR and Boot origins supply their own owner, never a first-task owner. *)
Definition mutex_del_callsite_entry_closed external platform critical sg original mask state : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform) &&
    mutex_del_interface_closed environment critical sg original mask state.

(** This split is used only by the local entry guard fragment. Before Save
    it is recombined with the dynamic world and handed over as one shared
    owner; it is not a private frame across an interruptible call. *)
Definition mutex_del_callsite_entry_support external platform sg original state : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform) &&
    (unmap_table_rep sg ** mutex_del_interface_context environment original **
      mutex_del_interface_capsules environment state).

Lemma mutex_del_callsite_entry_from_interface : forall environment critical sg original mask state,
  mutex_del_interface_closed environment critical sg original mask state |--
    mutex_del_callsite_entry_closed environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical sg original mask state.
Proof.
  intros; unfold mutex_del_callsite_entry_closed; Exists environment.
  unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_del_callsite_entry_split : forall external platform critical sg original mask state,
  mutex_del_callsite_entry_closed external platform critical sg original mask state |--
    mutex_query_closed platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) mask state **
    mutex_del_callsite_entry_support external platform sg original state.
Proof.
  intros; unfold mutex_del_callsite_entry_closed; Intros environment.
  unfold mutex_del_callsite_environment in H; destruct H as [Hexternal Hplatform].
  unfold mutex_del_interface_closed, kernel_program_closed, mutex_query_closed.
  unfold mutex_del_callsite_entry_support; Exists environment.
  unfold mutex_del_callsite_environment; rewrite Hplatform; entailer!.
Qed.

Lemma mutex_del_callsite_entry_merge : forall external platform critical sg original mask state,
  mutex_query_closed platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) mask state **
    mutex_del_callsite_entry_support external platform sg original state |--
  mutex_del_callsite_entry_closed external platform critical sg original mask state.
Proof.
  intros; unfold mutex_del_callsite_entry_support; Intros environment.
  unfold mutex_del_callsite_environment in H; destruct H as [Hexternal Hplatform].
  unfold mutex_del_callsite_entry_closed; Exists environment.
  unfold mutex_del_interface_closed, kernel_program_closed, mutex_query_closed,
    mutex_del_callsite_environment; rewrite Hplatform; entailer!.
Qed.

(** The actual acquired call/context/map source, not an unconditional Save
    Ensure. Program-history provenance is now established separately by
    the configured entry and transported through the same region interval;
    it is no longer a premise demanded of this physical source producer. *)
Definition mutex_del_callsite_acquired external platform critical sg original mask saved before entry : Assertion :=
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_call_save_source external environment.(mutex_del_call_port) critical sg
        original returned mask saved before entry /\
      mutex_del_interface_same_call returned original) &&
    (mutex_del_interface_context environment returned ** mutex_del_interface_capsules environment entry).

Definition mutex_del_callsite_cut environment sg cut state : Assertion :=
  kernel_client_heap_resources environment.(mutex_del_call_continuations)
    (mutex_del_creator_heap_resources environment.(mutex_del_call_continuations)) sg cut state.

(** The complete shared stage is passed to Restore. In particular Extra
    owns the creator ECB together with the one table and the entire map;
    there is no separately retained private Del frame across that call. *)
Definition mutex_del_callsite_restore_stage external platform critical sg original mask saved
  before entry released : Assertion :=
  EX environment returned cut,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_call_save_source external environment.(mutex_del_call_port) critical sg
        original returned mask saved before entry /\
      mutex_del_interface_same_call returned original) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved entry **
     mutex_del_interface_context environment returned **
     mutex_del_callsite_cut environment sg cut released).

(** Both the history index and the actual returned cut are explicit.
    No equality current=released or cut=Closed is promised. The relation
    is a call-site proof obligation, not an installed CPU ABI contract. *)
Definition mutex_del_callsite_restore_return external platform critical sg original mask
  released returned current cut : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_resumption_task_source_trace external environment.(mutex_del_call_port)
        critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
        original.(os_sched_call_origin) released false returned.(os_sched_call_origin) current /\
      mutex_del_interface_same_call returned original) &&
    (kernel_call_execution_owned external platform returned mask **
      mutex_del_callsite_cut environment sg cut current).

Definition mutex_del_callsite_unscheduled_post external platform critical sg original mask released : Assertion :=
  EX returned current cut,
    mutex_del_callsite_restore_return external platform critical sg original mask released returned current cut.

Definition mutex_del_callsite_restore_facts external platform critical sg original released returned current : Prop :=
  exists environment,
    mutex_del_callsite_environment environment external platform /\
    kernel_resumption_task_source_trace external environment.(mutex_del_call_port)
      critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
      original.(os_sched_call_origin) released false returned.(os_sched_call_origin) current /\
    mutex_del_interface_same_call returned original.

(** The scheduling source owner must return the same complete resource
    family at its REAL final state. An old dynamic-only os_sched_post does
    not establish this predicate by itself. *)
Definition mutex_del_callsite_sched_return external platform critical sg original mask before : Assertion :=
  EX environment entry returned current cut,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      critical_region_interval critical sg original.(os_sched_call_invocation) before entry /\
      os_sched_c_return external critical sg entry original returned current /\
      mutex_del_interface_same_call returned original) &&
    (kernel_call_execution_owned external platform returned mask **
      mutex_del_callsite_cut environment sg cut current).

(** A scheduled deletion has TWO source histories: the actual Restore
    return that precedes OS_Sched, then OS_Sched's actual return. *)
Definition mutex_del_callsite_scheduled_post external platform critical sg original mask released : Assertion :=
  EX restored acquired,
    coq_prop (mutex_del_callsite_restore_facts external platform critical sg original
      released restored acquired) &&
    mutex_del_callsite_sched_return external platform critical sg restored mask acquired.

Lemma mutex_del_callsite_restore_open : forall external platform critical sg original mask released,
  mutex_del_callsite_unscheduled_post external platform critical sg original mask released |--
    EX returned current cut,
      coq_prop (mutex_del_callsite_restore_facts external platform critical sg original released returned current) &&
      mutex_del_callsite_restore_return external platform critical sg original mask released returned current cut.
Proof.
  intros external platform critical sg original mask released heap
    [returned [current [cut [environment [Hfacts Howned]]]]].
  exists returned, current, cut; split.
  - exists environment; exact Hfacts.
  - exists environment; split; assumption.
Qed.

Lemma mutex_del_recheck_typed_cut : forall environment sg pointer eid state,
  mutex_del_recheck_whole sg pointer eid state ** mutex_del_interface_capsules environment state |--
    EX cut, mutex_del_callsite_cut environment sg cut state.
Proof.
  intros environment sg pointer eid state heap
    [owned [caps [Hjoin [[Hpublic|Hprivate] Hcaps]]]].
  - destruct Hpublic as [event [Hfacts Hworld]].
    exists KernelClientHeapClosed.
    unfold mutex_del_callsite_cut; cbn [kernel_client_heap_resources].
    exists owned, caps; split; [exact Hjoin|split; assumption].
  - destruct Hprivate as [allocation [[Hpointer [Hget Hsource]] Hworld]].
    exists (KernelClientHeapExtra pointer).
    assert (Hclose : (kernel_program_inv sg state ** event_private_storage_rep sg eid allocation) **
        mutex_del_interface_capsules environment state |--
      mutex_del_callsite_cut environment sg (KernelClientHeapExtra pointer) state).
    { unfold mutex_del_callsite_cut; cbn [kernel_client_heap_resources].
      unfold mutex_del_creator_heap_resources; Exists eid allocation.
      unfold kernel_client_heap_world, mutex_del_interface_capsules; entailer!. }
    apply Hclose; exists owned, caps; split; [exact Hjoin|split; assumption].
Qed.

Lemma mutex_del_callsite_recheck_restore_stage : forall external platform critical sg original
  mask saved before entry pointer eid,
  critical_region_masked platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) saved entry **
    mutex_del_recheck_whole sg pointer eid entry **
    mutex_del_callsite_acquired external platform critical sg original mask saved before entry |--
  mutex_del_callsite_restore_stage external platform critical sg original mask saved before entry entry.
Proof.
  intros; unfold mutex_del_callsite_acquired; Intros environment returned.
  sep_apply_l_atomic (mutex_del_recheck_typed_cut environment sg pointer eid entry).
  Intros cut; unfold mutex_del_callsite_restore_stage; Exists environment returned cut; entailer!.
Qed.

Lemma mutex_del_callsite_program_restore_stage : forall external platform critical sg original
  mask saved before entry released,
  released.(TskState).(parkedTaskStacks) = entry.(TskState).(parkedTaskStacks) ->
  critical_region_masked platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) saved entry ** kernel_program_inv sg released **
    mutex_del_callsite_acquired external platform critical sg original mask saved before entry |--
  mutex_del_callsite_restore_stage external platform critical sg original mask saved before entry released.
Proof.
  intros; unfold mutex_del_callsite_acquired; Intros environment returned.
  unfold mutex_del_callsite_restore_stage; Exists environment returned KernelClientHeapClosed.
  unfold mutex_del_callsite_cut; cbn [kernel_client_heap_resources].
  unfold kernel_client_heap_world, mutex_del_interface_capsules; rewrite H; entailer!.
Qed.
