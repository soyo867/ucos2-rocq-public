Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_stack_equiv_spec.
Require Import Coq.Logic.FunctionalExtensionality.

(** Generic-local forms of Del's existing public C-call contracts.
    Exact errors, observations and conditional task admission stay unchanged.
    The definition is an interface; concrete C/port producers discharge it. *)
Section ContinuationContracts.
Variable source_env : MutexDelCallEnvironment.

Definition mutex_del_continuation_save_pre external platform (critical : CriticalRegionResources)
  saved_local sg original mask state : Assertion :=
  mutex_del_continuation_entry source_env external platform saved_local sg original mask state.

Definition mutex_del_continuation_restore_pre external platform critical saved_local sg original mask saved
  acquired checkpoint : Assertion :=
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved /\ environment = source_env) &&
    kernel_continuation_call_masked environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg (task_stack_call_active_key original)
      returned saved acquired checkpoint.

Lemma mutex_del_continuation_program_restore_merge : forall external platform critical saved_local sg original
  mask saved before acquired checkpoint,
  mutex_del_stack_checkpoint sg acquired checkpoint ->
  mutex_del_runtime_program_restore_pre platform critical sg original mask saved before acquired checkpoint **
    mutex_del_continuation_acquired source_env external platform saved_local sg original acquired |--
  mutex_del_continuation_restore_pre external platform critical saved_local sg original mask saved acquired checkpoint.
Proof.
  intros external platform critical saved_local sg original mask saved before acquired checkpoint Hcheckpoint.
  unfold mutex_del_runtime_program_restore_pre; Intros_p Hfacts.
  destruct Hfacts as [Hsource [Hvalid Hsaved]].
  sep_apply_l_atomic (mutex_del_continuation_restore_stage source_env external platform critical saved_local sg original saved acquired checkpoint
    Hcheckpoint); Intros environment returned.
  unfold mutex_del_continuation_restore_pre; Exists environment returned; entailer!.
Qed.

Definition mutex_del_continuation_return_at external platform saved_local sg original mask returned current : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\ environment = source_env) &&
    kernel_continuation_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg (task_stack_call_active_key original) returned mask current.

Definition mutex_del_continuation_return external platform saved_local sg original mask : Assertion :=
  EX returned current, mutex_del_continuation_return_at external platform saved_local sg original mask returned current.

Lemma mutex_del_continuation_return_open : forall external platform saved_local sg original mask,
  mutex_del_continuation_return external platform saved_local sg original mask |--
  EX returned current,
    coq_prop (kernel_stack_call_same_call returned original) &&
    mutex_del_continuation_return_at external platform saved_local sg original mask returned current.
Proof.
  intros; unfold mutex_del_continuation_return, mutex_del_continuation_return_at; Intros returned current environment.
  Exists returned current environment; entailer!.
Qed.

Lemma mutex_del_continuation_return_sched_pre : forall external platform saved_local sg original mask returned current,
  mutex_del_continuation_return_at external platform saved_local sg original mask returned current |--
  mutex_del_continuation_entry source_env external platform saved_local sg returned mask current.
Proof.
  intros; unfold mutex_del_continuation_return_at; Intros environment.
  destruct H as [Henv [[Hi [Ho Hs]] Hsource]].
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite Ho; reflexivity. }
  unfold mutex_del_continuation_entry; Exists environment; rewrite Hactive; entailer!.
Qed.

Lemma mutex_del_continuation_return_same_call : forall external platform saved_local sg original resumed mask,
  kernel_stack_call_same_call resumed original ->
  mutex_del_continuation_return external platform saved_local sg resumed mask |--
  mutex_del_continuation_return external platform saved_local sg original mask.
Proof.
  intros external platform saved_local sg original resumed mask [Hi [Ho Hs]].
  unfold mutex_del_continuation_return, mutex_del_continuation_return_at; Intros returned current environment.
  destruct H as [Henv [[Hi' [Ho' Hs']] Hsource]].
  assert (Hsame : kernel_stack_call_same_call returned original).
  { unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hactive : task_stack_call_active_key resumed = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite Ho; reflexivity. }
  Exists returned current environment; rewrite Hactive; entailer!.
Qed.

Lemma mutex_del_continuation_sched_pre : forall environment saved_local sg original mask before,
  kernel_continuation_call_closed environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key original) original mask before |--
  os_sched_continuation_pre (mutex_del_runtime_sched_environment environment)
    saved_local mutex_del_stack_resources sg original mask before.
Proof. reflexivity. Qed.

Lemma mutex_del_continuation_sched_post : forall environment saved_local sg original mask before,
  environment = source_env ->
  os_sched_continuation_return_post (mutex_del_runtime_sched_environment environment)
    saved_local mutex_del_stack_resources sg original mask before |--
  mutex_del_continuation_return environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) saved_local sg original mask.
Proof.
  intros environment saved_local sg original mask before Henv.
  unfold os_sched_continuation_return_post; Intros returned current.
  destruct H as [Hsame Hsource].
  destruct Hsame as [Hi [Ho Hs]].
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite Ho; reflexivity. }
  unfold mutex_del_continuation_return, mutex_del_continuation_return_at; Exists returned current environment.
  cbn [mutex_del_runtime_sched_environment task_stack_call_continuations].
  rewrite Hactive; unfold mutex_del_callsite_environment, kernel_stack_call_same_call; entailer!.
Qed.

Definition mutex_del_continuation_post external platform saved_local sg original mask before pe option eid result error : Assertion :=
  (coq_prop (exists code, mutex_del_before_save_error pe
      (event_slot_type_value before.(EventState) eid) before.(IntrState).(intNesting) =
      Some (result, code) /\ error = encode_os_err_code code) &&
    mutex_del_continuation_entry source_env external platform saved_local sg original mask before) ||
  (EX acquired checkpoint request,
    coq_prop (mutex_del_parent_prefix_ok pe before eid /\
      mutex_owner_source_history sg before acquired /\
      mutex_del_parent_critical_observation sg eid option result error request acquired checkpoint) &&
    mutex_del_continuation_return external platform saved_local sg original mask) ||
  (EX acquired kind,
    coq_prop (mutex_del_parent_prefix_ok pe before eid /\
      mutex_owner_source_history sg before acquired /\
      mutex_del_runtime_type_observation sg eid acquired kind /\ kind <> 4 /\
      result = pe /\ error = encode_os_err_code OS_ERR_EVENT_TYPE) &&
    mutex_del_continuation_return external platform saved_local sg original mask).

Lemma mutex_del_continuation_critical_return : forall external platform saved_local sg original mask saved
  before acquired checkpoint pe option eid result error request,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_del_runtime_save_facts sg mask saved before acquired ->
  mutex_del_parent_critical_observation sg eid option result error request acquired checkpoint ->
  mutex_del_continuation_return external platform saved_local sg original mask |--
  mutex_del_continuation_post external platform saved_local sg original mask before pe option eid result error.
Proof.
  intros external platform saved_local sg original mask saved before acquired checkpoint pe option eid result error request
    Hprefix [Hhistory Hrest] Hobservation heap Hpost.
  left; right; exists acquired, checkpoint, request;
    split; [exact (conj Hprefix (conj Hhistory Hobservation))|exact Hpost].
Qed.

Lemma mutex_del_continuation_type_error_return : forall external platform saved_local sg original mask saved
  before acquired pe option eid kind,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_del_runtime_save_facts sg mask saved before acquired ->
  mutex_del_runtime_type_observation sg eid acquired kind -> kind <> 4 ->
  mutex_del_continuation_return external platform saved_local sg original mask |--
  mutex_del_continuation_post external platform saved_local sg original mask before pe option eid pe
    (encode_os_err_code OS_ERR_EVENT_TYPE).
Proof.
  intros external platform saved_local sg original mask saved before acquired pe option eid kind
    Hprefix [Hhistory Hrest] Hobservation Hkind heap Hpost.
  right; exists acquired, kind;
    split; [exact (conj Hprefix (conj Hhistory (conj Hobservation
      (conj Hkind (conj eq_refl eq_refl)))))|exact Hpost].
Qed.

End ContinuationContracts.

Lemma mutex_del_continuation_return_at_emp_equiv : forall source_env external platform
  sg original mask returned current,
  mutex_del_continuation_return_at source_env external platform (fun _ => emp)
    sg original mask returned current --||--
  mutex_del_runtime_return_at source_env external platform sg original mask returned current.
Proof.
  intros source_env external platform sg original mask returned current.
  assert (Hlocal : task_create_continuation_local (fun _ => emp) = (fun _ => emp)).
  { apply functional_extensionality; intros descriptor.
    unfold task_create_continuation_local; destruct descriptor.(armv7a_continuation_call); reflexivity. }
  unfold mutex_del_continuation_return_at, mutex_del_runtime_return_at.
  rewrite Hlocal; split; Intros environment; Exists environment.
  - sep_apply_l_atomic (proj1 (kernel_continuation_call_closed_emp_equiv _ _ _
      environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
      (task_stack_call_active_key original) returned mask current)); entailer!.
  - sep_apply_l_atomic (proj2 (kernel_continuation_call_closed_emp_equiv _ _ _
      environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
      (task_stack_call_active_key original) returned mask current)); entailer!.
Qed.

Lemma mutex_del_continuation_return_emp_equiv : forall source_env external platform sg original mask,
  mutex_del_continuation_return source_env external platform (fun _ => emp) sg original mask --||--
  mutex_del_runtime_return source_env external platform sg original mask.
Proof.
  intros; unfold mutex_del_continuation_return, mutex_del_runtime_return.
  split; Intros returned current; Exists returned current.
  - apply (proj1 (mutex_del_continuation_return_at_emp_equiv source_env external platform
      sg original mask returned current)).
  - apply (proj2 (mutex_del_continuation_return_at_emp_equiv source_env external platform
      sg original mask returned current)).
Qed.

(** Exact compatibility includes all ordered early errors, the recheck
    Type error, and successful/critical returns. Nothing is success-only. *)
Lemma mutex_del_continuation_post_emp_equiv : forall source_env external platform
  sg original mask before pe option eid result error,
  mutex_del_continuation_post source_env external platform (fun _ => emp)
    sg original mask before pe option eid result error --||--
  mutex_del_runtime_post source_env external platform sg original mask before pe option eid result error.
Proof.
  intros source_env external platform sg original mask before pe option eid result error.
  destruct (mutex_del_continuation_entry_emp_equiv source_env external platform sg original mask before)
    as [Hentry Hentry_back].
  destruct (mutex_del_continuation_return_emp_equiv source_env external platform sg original mask)
    as [Hreturn Hreturn_back].
  unfold mutex_del_continuation_post, mutex_del_runtime_post.
  split; intros heap Hpost; destruct Hpost as [[Hearly|Hcritical]|Htype].
  - destruct Hearly as [Hfacts Howned]; left; left; split; [exact Hfacts|apply Hentry; exact Howned].
  - destruct Hcritical as [acquired [checkpoint [request [Hfacts Howned]]]].
    left; right; exists acquired, checkpoint, request; split; [exact Hfacts|apply Hreturn; exact Howned].
  - destruct Htype as [acquired [kind [Hfacts Howned]]].
    right; exists acquired, kind; split; [exact Hfacts|apply Hreturn; exact Howned].
  - destruct Hearly as [Hfacts Howned]; left; left; split; [exact Hfacts|apply Hentry_back; exact Howned].
  - destruct Hcritical as [acquired [checkpoint [request [Hfacts Howned]]]].
    left; right; exists acquired, checkpoint, request; split; [exact Hfacts|apply Hreturn_back; exact Howned].
  - destruct Htype as [acquired [kind [Hfacts Howned]]].
    right; exists acquired, kind; split; [exact Hfacts|apply Hreturn_back; exact Howned].
Qed.
