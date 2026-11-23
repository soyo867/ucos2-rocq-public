Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.

(** The same stage/admission and ordered error semantics are used by the
    new canonical annotation. Only its owned parked map is parameterized.
    Existing source families do not acquire arbitrary locals by this change. *)

Definition mutex_del_continuation_source_entry environment external platform saved_local sg call mask state : Assertion :=
  coq_prop (mutex_del_call_stage call state /\ kernel_call_stack_available call state) &&
  mutex_del_continuation_entry environment external platform saved_local sg call mask state.

(** The normal-call cut is required only beyond the existing ordered
    NULL/Type/ISR checks. It is the existing parked-map observation, not
    another ghost field or a promise about future scheduling. Boot has no
    active task key. The entry producers below establish the observation
    from the already selected/returned map. *)
Definition mutex_del_continuation_call_admission call state pe eid : Prop :=
  mutex_del_parent_prefix_ok pe state eid ->
  mutex_del_call_stage call state /\ kernel_call_stack_available call state.

Definition mutex_del_continuation_source_input environment external platform saved_local sg call mask state pe eid : Assertion :=
  coq_prop (mutex_del_continuation_call_admission call state pe eid) &&
  mutex_del_continuation_entry environment external platform saved_local sg call mask state.

Lemma mutex_del_continuation_source_entry_admission : forall environment external platform saved_local sg call mask state pe eid,
  mutex_del_continuation_source_entry environment external platform saved_local sg call mask state |--
  mutex_del_continuation_source_input environment external platform saved_local sg call mask state pe eid.
Proof.
  intros; unfold mutex_del_continuation_source_entry, mutex_del_continuation_source_input,
    mutex_del_continuation_call_admission; entailer!.
Qed.

Lemma mutex_del_continuation_source_input_early_return : forall environment external platform saved_local sg call mask state pe eid error,
  mutex_del_before_save_error pe (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) = Some error ->
  mutex_del_continuation_entry environment external platform saved_local sg call mask state |--
  mutex_del_continuation_source_input environment external platform saved_local sg call mask state pe eid.
Proof.
  intros; unfold mutex_del_continuation_source_input, mutex_del_continuation_call_admission, mutex_del_parent_prefix_ok;
    entailer!; congruence.
Qed.

Lemma mutex_del_continuation_source_input_continue : forall environment external platform saved_local sg call mask state pe eid,
  mutex_del_parent_prefix_ok pe state eid ->
  mutex_del_continuation_source_input environment external platform saved_local sg call mask state pe eid |--
  mutex_del_continuation_source_entry environment external platform saved_local sg call mask state.
Proof.
  intros; unfold mutex_del_continuation_source_input, mutex_del_continuation_source_entry,
    mutex_del_continuation_call_admission;
    entailer!; auto.
Qed.

Definition mutex_del_continuation_source_save_post environment external platform critical saved_local sg original mask saved before
  : Assertion :=
  EX acquired,
    coq_prop (mutex_del_call_stage original acquired /\ kernel_call_stack_available original acquired /\
      mutex_del_runtime_save_facts sg mask saved before acquired) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved acquired ** kernel_program_inv sg acquired **
     mutex_del_continuation_acquired environment external platform saved_local sg original acquired).

Lemma mutex_del_continuation_source_save_post_from_masked : forall environment critical saved_local sg original returned
  mask saved before acquired,
  mutex_del_call_stage original acquired -> kernel_call_stack_available original acquired ->
  mutex_owner_source_history sg before acquired ->
  kernel_stack_call_same_call returned original -> interrupt_saved_value mask saved ->
  kernel_continuation_call_masked environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg (task_stack_call_active_key original)
    returned saved acquired acquired |--
  mutex_del_continuation_source_save_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local sg original returned mask saved before acquired
    Hstage Havailable Hhistory Hsame Hsaved.
  destruct Hsame as [Hi [Ho Hstack]].
  unfold kernel_continuation_call_masked, kernel_continuation_inv, mutex_del_stack_resources.
  unfold mutex_del_continuation_source_save_post; Exists acquired.
  unfold mutex_del_continuation_acquired, mutex_del_continuation_stack_support; Exists environment returned.
  unfold mutex_del_runtime_save_facts, kernel_stack_call_same_call,
    mutex_del_callsite_environment, kernel_program_inv; rewrite Hi, Ho; entailer!.
Qed.

Lemma mutex_del_continuation_source_save_post_forget : forall environment external platform critical saved_local sg original mask saved before,
  mutex_del_continuation_source_save_post environment external platform critical saved_local sg original mask saved before |--
  mutex_del_continuation_save_post environment external platform critical saved_local sg original mask saved before.
Proof.
  intros; unfold mutex_del_continuation_source_save_post, mutex_del_continuation_save_post; Intros acquired.
  Exists acquired; entailer!.
Qed.

Definition mutex_del_continuation_source_save_pre environment external platform
  (critical : CriticalRegionResources) saved_local sg call mask state : Assertion :=
  mutex_del_continuation_source_entry environment external platform saved_local sg call mask state.

Definition mutex_del_continuation_source_restore_pre environment external platform critical
  saved_local sg original mask saved acquired checkpoint : Assertion :=
  coq_prop (mutex_del_call_stage original checkpoint /\ kernel_call_stack_available original checkpoint) &&
  mutex_del_continuation_restore_pre environment external platform critical saved_local sg
    original mask saved acquired checkpoint.

Definition mutex_del_continuation_source_return_at environment external platform
  saved_local sg original mask returned current : Assertion :=
  coq_prop (mutex_del_call_stage returned current /\ kernel_call_stack_available returned current) &&
  mutex_del_continuation_return_at environment external platform saved_local sg original mask returned current.

Definition mutex_del_continuation_source_return environment external platform saved_local sg original mask : Assertion :=
  EX returned current,
    mutex_del_continuation_source_return_at environment external platform saved_local sg original mask returned current.

Definition mutex_del_continuation_source_sched_pre environment external platform
  saved_local sg original mask current : Assertion :=
  coq_prop (mutex_del_task_call_stage original current /\ kernel_call_stack_available original current) &&
  mutex_del_continuation_entry environment external platform saved_local sg original mask current.

Lemma mutex_del_continuation_source_save_admission : forall environment external platform critical
  saved_local sg call mask state pe eid,
  mutex_del_continuation_call_admission call state pe eid ->
  mutex_del_parent_prefix_ok pe state eid ->
  mutex_del_continuation_entry environment external platform saved_local sg call mask state |--
  mutex_del_continuation_source_save_pre environment external platform critical saved_local sg call mask state.
Proof.
  intros environment external platform critical saved_local sg call mask state pe eid Hadmission Hprefix.
  unfold mutex_del_continuation_source_save_pre, mutex_del_continuation_source_entry.
  specialize (Hadmission Hprefix); entailer!.
Qed.

Lemma mutex_del_continuation_source_restore_merge : forall environment external platform critical
  saved_local sg original mask saved before acquired checkpoint,
  mutex_del_stack_checkpoint sg acquired checkpoint ->
  mutex_del_call_stage original checkpoint ->
  kernel_call_stack_available original checkpoint ->
  mutex_del_runtime_program_restore_pre platform critical sg original mask saved before acquired checkpoint **
    mutex_del_continuation_acquired environment external platform saved_local sg original acquired |--
  mutex_del_continuation_source_restore_pre environment external platform critical saved_local sg original mask saved acquired checkpoint.
Proof.
  intros; unfold mutex_del_continuation_source_restore_pre.
  sep_apply_l_atomic (mutex_del_continuation_program_restore_merge environment external platform
    critical saved_local sg original mask saved before acquired checkpoint H).
  entailer!.
Qed.

Lemma mutex_del_continuation_source_return_at_forget : forall environment external platform
  saved_local sg original mask returned current,
  mutex_del_continuation_source_return_at environment external platform saved_local sg original mask returned current |--
  mutex_del_continuation_return_at environment external platform saved_local sg original mask returned current.
Proof. intros; unfold mutex_del_continuation_source_return_at; entailer!. Qed.

Lemma mutex_del_continuation_source_return_forget : forall environment external platform saved_local sg original mask,
  mutex_del_continuation_source_return environment external platform saved_local sg original mask |--
  mutex_del_continuation_return environment external platform saved_local sg original mask.
Proof.
  intros; unfold mutex_del_continuation_source_return, mutex_del_continuation_return; Intros returned current.
  Exists returned current; apply mutex_del_continuation_source_return_at_forget.
Qed.

Lemma mutex_del_continuation_source_return_open : forall environment external platform saved_local sg original mask,
  mutex_del_continuation_source_return environment external platform saved_local sg original mask |--
  EX returned current,
    coq_prop (kernel_stack_call_same_call returned original) &&
    mutex_del_continuation_source_return_at environment external platform saved_local sg original mask returned current.
Proof.
  intros; unfold mutex_del_continuation_source_return, mutex_del_continuation_source_return_at,
    mutex_del_continuation_return_at; Intros returned current selected.
  Exists returned current selected; entailer!.
Qed.

Lemma mutex_del_continuation_source_return_sched_pre : forall environment external platform
  saved_local sg original mask returned current,
  mutex_del_schedule_request original 1 ->
  mutex_del_continuation_source_return_at environment external platform saved_local sg original mask returned current |--
  mutex_del_continuation_source_sched_pre environment external platform saved_local sg returned mask current.
Proof.
  intros environment external platform saved_local sg original mask returned current Hrequest.
  unfold mutex_del_continuation_source_return_at; Intros_p Hfacts.
  destruct Hfacts as [Hcurrent Havailable].
  assert (Hopen : mutex_del_continuation_return_at environment external platform
      saved_local sg original mask returned current |--
    coq_prop (kernel_stack_call_same_call returned original) &&
    mutex_del_continuation_return_at environment external platform saved_local sg original mask returned current).
  { unfold mutex_del_continuation_return_at; Intros selected; Exists selected; entailer!. }
  sep_apply_l_atomic Hopen; Intros_p Hsame.
  assert (Htask : mutex_del_task_call_stage returned current).
  { destruct Hsame as [Hi [Ho Hstack]].
    unfold mutex_del_call_stage in Hcurrent.
    destruct returned.(os_sched_call_origin) eqn:Horigin; [|exact Hcurrent].
    exfalso; apply (Hrequest eq_refl); symmetry; exact Ho. }
  unfold mutex_del_continuation_source_sched_pre.
  apply _derivable1_andp_intros; [entailer!|].
  apply mutex_del_continuation_return_sched_pre.
Qed.

(** Existing Boot/selected/sequential entry producers remain usable at
    their actual emp instance, without erasing a general saved-local map. *)
Lemma mutex_del_continuation_source_entry_emp_equiv : forall environment external platform
  sg call mask state,
  mutex_del_continuation_source_entry environment external platform (fun _ => emp) sg call mask state --||--
  coq_prop (kernel_call_stack_available call state) &&
    mutex_del_source_entry environment external platform sg call mask state.
Proof.
  intros; unfold mutex_del_continuation_source_entry, mutex_del_source_entry.
  destruct (mutex_del_continuation_entry_emp_equiv environment external platform sg call mask state)
    as [Hforward Hbackward].
  split.
  - intros heap [[Hstage Havailable] Howned]; split; [exact Havailable|].
    split; [exact Hstage|apply Hforward; exact Howned].
  - intros heap [Havailable [Hstage Howned]]; split.
    + exact (conj Hstage Havailable).
    + apply Hbackward; exact Howned.
Qed.

Lemma mutex_del_continuation_source_return_emp_equiv : forall environment external platform sg original mask,
  mutex_del_continuation_source_return environment external platform (fun _ => emp) sg original mask --||--
  EX returned current, coq_prop (kernel_call_stack_available returned current) &&
    mutex_del_source_return_at environment external platform sg original mask returned current.
Proof.
  intros; unfold mutex_del_continuation_source_return,
    mutex_del_continuation_source_return_at, mutex_del_source_return_at.
  split.
  - intros heap [returned [current [[Hstage Havailable] Howned]]].
    exists returned, current; split; [exact Havailable|]. split; [exact Hstage|].
    apply (proj1 (mutex_del_continuation_return_at_emp_equiv environment external platform
      sg original mask returned current)); exact Howned.
  - intros heap [returned [current [Havailable [Hstage Howned]]]].
    exists returned, current; split; [exact (conj Hstage Havailable)|].
    apply (proj2 (mutex_del_continuation_return_at_emp_equiv environment external platform
      sg original mask returned current)); exact Howned.
Qed.

(** Del's actual masked writes never change the parked map. This is the
    pure fact consumed at both recycle-to-Restore annotation joins; it
    does not transport absence through an interruptible interval. *)
Lemma mutex_del_critical_preserves_call_available : forall sg eid option entry result checkpoint call,
  mutex_del_critical sg eid option entry result checkpoint ->
  kernel_call_stack_available call entry -> kernel_call_stack_available call checkpoint.
Proof.
  intros sg eid option entry result checkpoint call Hrun Havailable.
  destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hrun)
    as [_ [Hstacks _]].
  unfold kernel_call_stack_available in *; destruct call.(os_sched_call_origin); [exact I|].
  rewrite Hstacks; exact Havailable.
Qed.

Lemma mutex_del_observation_preserves_call_available : forall sg eid option result code request
  entry checkpoint call,
  mutex_del_parent_critical_observation sg eid option result code request entry checkpoint ->
  kernel_call_stack_available call entry -> kernel_call_stack_available call checkpoint.
Proof.
  intros sg eid option result code request entry checkpoint call [error [scheduled [Hrun _]]] Havailable.
  eapply mutex_del_critical_preserves_call_available; eassumption.
Qed.

(** The shared Scheduler C precondition is established from this caller's
    existing stage and the returned normal cut. Selection-disabled paths
    need no nonempty-ready or storage fact. No ready-client certificate is
    fabricated here; the linked region owns that separate module proof. *)
Lemma mutex_del_continuation_sched_call_pre : forall environment external platform saved_local
  sg original mask current,
  (forall base, tcb_field_address base TCBStkPtr = base) ->
  mutex_del_continuation_source_sched_pre environment external platform saved_local
    sg original mask current |--
  os_sched_continuation_call_pre (mutex_del_runtime_sched_environment environment)
    saved_local mutex_del_stack_resources sg original mask current.
Proof.
  intros environment external platform saved_local sg original mask current Haddress.
  unfold mutex_del_continuation_source_sched_pre; Intros_p Hfacts.
  destruct Hfacts as [Hstage Havailable].
  unfold mutex_del_continuation_entry; Intros selected.
  destruct H as [Henvironment ->].
  assert (Hvalid : kernel_continuation_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key original) original mask current |--
    coq_prop (UCOS2_state_inv sg current) &&
      kernel_continuation_call_closed environment.(mutex_del_call_continuations)
        mutex_del_stack_resources (task_create_continuation_local saved_local) sg
        (task_stack_call_active_key original) original mask current).
  { unfold kernel_continuation_call_closed, kernel_continuation_inv,
      mutex_del_stack_resources, kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalid; Intros_p Hstate.
  assert (Hcut : os_sched_call_cut sg original current).
  { destruct (os_sched_selection_enabled current) eqn:Henabled.
    - eapply os_sched_call_cut_from_source; [exact Hstate|exact (proj1 Hstage)| |exact Havailable|apply Haddress].
      eapply mutex_del_task_call_stage_ready; eassumption.
    - apply os_sched_call_cut_disabled; exact Henabled. }
  unfold os_sched_continuation_call_pre, os_sched_continuation_pre,
    mutex_del_runtime_sched_environment; cbn [task_stack_call_continuations]; entailer!.
Qed.
