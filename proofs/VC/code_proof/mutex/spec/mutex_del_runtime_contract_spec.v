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

Section RuntimeContracts.
Variable source_env : MutexDelCallEnvironment.

(** This named pre binds the selected critical-region interpretation at
    the macro call. It owns exactly the runtime entry, with no added fact. *)
Definition mutex_del_runtime_save_pre external platform (critical : CriticalRegionResources)
  sg original mask state : Assertion :=
  mutex_del_runtime_entry source_env external platform sg original mask state.

(** Modular C-call interfaces. Their definitions are NOT total platform
    contracts: the actual checked source families are connected separately.
    Every returning call owns the current world rather than an old snapshot. *)
Definition mutex_del_runtime_program_restore_pre platform critical sg original mask saved
  before acquired checkpoint : Assertion :=
  coq_prop (mutex_del_runtime_save_facts sg mask saved before acquired) &&
  (critical_region_masked platform critical sg original.(os_sched_call_invocation)
     original.(os_sched_call_origin) saved acquired ** kernel_program_inv sg checkpoint).

Definition mutex_del_runtime_restore_pre external platform critical sg original mask saved
  acquired checkpoint : Assertion :=
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved /\ environment = source_env) &&
    kernel_stack_call_masked environment.(mutex_del_call_continuations)
      mutex_del_stack_resources critical sg (task_stack_call_active_key original)
      returned saved acquired checkpoint.

Lemma mutex_del_runtime_program_restore_merge : forall external platform critical sg original
  mask saved before acquired checkpoint,
  mutex_del_stack_checkpoint sg acquired checkpoint ->
  mutex_del_runtime_program_restore_pre platform critical sg original mask saved before acquired checkpoint **
    mutex_del_runtime_acquired source_env external platform sg original acquired |--
  mutex_del_runtime_restore_pre external platform critical sg original mask saved acquired checkpoint.
Proof.
  intros external platform critical sg original mask saved before acquired checkpoint Hcheckpoint.
  unfold mutex_del_runtime_program_restore_pre; Intros_p Hfacts.
  destruct Hfacts as [Hsource [Hvalid Hsaved]].
  sep_apply_l_atomic (mutex_del_runtime_restore_stage source_env external platform critical sg original saved acquired checkpoint
    Hcheckpoint); Intros environment returned.
  unfold mutex_del_runtime_restore_pre; Exists environment returned; entailer!.
Qed.

Definition mutex_del_runtime_return_at external platform sg original mask returned current : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\ environment = source_env) &&
    kernel_stack_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources sg (task_stack_call_active_key original) returned mask current.

Definition mutex_del_runtime_return external platform sg original mask : Assertion :=
  EX returned current, mutex_del_runtime_return_at external platform sg original mask returned current.

Lemma mutex_del_runtime_return_open : forall external platform sg original mask,
  mutex_del_runtime_return external platform sg original mask |--
  EX returned current,
    coq_prop (kernel_stack_call_same_call returned original) &&
    mutex_del_runtime_return_at external platform sg original mask returned current.
Proof.
  intros; unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Intros returned current environment.
  Exists returned current environment; entailer!.
Qed.

Lemma mutex_del_runtime_return_sched_pre : forall external platform sg original mask returned current,
  mutex_del_runtime_return_at external platform sg original mask returned current |--
  mutex_del_runtime_entry source_env external platform sg returned mask current.
Proof.
  intros; unfold mutex_del_runtime_return_at; Intros environment.
  destruct H as [Henv [[Hi [Ho Hs]] Hsource]].
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite Ho; reflexivity. }
  unfold mutex_del_runtime_entry; Exists environment; rewrite Hactive; entailer!.
Qed.

Lemma mutex_del_runtime_return_same_call : forall external platform sg original resumed mask,
  kernel_stack_call_same_call resumed original ->
  mutex_del_runtime_return external platform sg resumed mask |--
  mutex_del_runtime_return external platform sg original mask.
Proof.
  intros external platform sg original resumed mask [Hi [Ho Hs]].
  unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Intros returned current environment.
  destruct H as [Henv [[Hi' [Ho' Hs']] Hsource]].
  assert (Hsame : kernel_stack_call_same_call returned original).
  { unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hactive : task_stack_call_active_key resumed = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite Ho; reflexivity. }
  Exists returned current environment; rewrite Hactive; entailer!.
Qed.

(** Repackage the SAME ABI/port; constructing this record adds no resource
    or behavior law. It is consumed at Del's actual optional scheduler call. *)
Definition mutex_del_runtime_sched_environment environment : TaskStackCallEnvironment :=
  {| task_stack_call_external := environment.(mutex_del_call_external);
     task_stack_call_platform := environment.(mutex_del_call_platform);
     task_stack_call_port := environment.(mutex_del_call_port);
     task_stack_call_continuations := environment.(mutex_del_call_continuations) |}.

Lemma mutex_del_runtime_sched_pre : forall environment sg original mask before,
  kernel_stack_call_closed environment.(mutex_del_call_continuations) mutex_del_stack_resources
    sg (task_stack_call_active_key original) original mask before |--
  os_sched_stack_pre (mutex_del_runtime_sched_environment environment)
    mutex_del_stack_resources sg original mask before.
Proof. reflexivity. Qed.

Lemma mutex_del_runtime_sched_post : forall environment sg original mask before,
  environment = source_env ->
  os_sched_stack_return_post (mutex_del_runtime_sched_environment environment)
    mutex_del_stack_resources sg original mask before |--
  mutex_del_runtime_return environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg original mask.
Proof.
  intros; unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post; Intros returned current.
  unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned current environment.
  cbn [mutex_del_runtime_sched_environment task_stack_call_continuations].
  unfold mutex_del_callsite_environment; entailer!.
Qed.

(** The original error ordering and critical result are retained. The
    returned current object need not stay deleted: Restore/OS_Sched may
    allow real recycling/reuse. The historical observation still records
    the exact return/error, owner-priority and waiter/recycle effects.
    Request=1 is executed by the C control flow before the returned owner
    is accepted; no flat scheduler body history is demanded afterwards. *)
Definition mutex_del_runtime_post external platform sg original mask before pe option eid result error : Assertion :=
  (coq_prop (exists code, mutex_del_before_save_error pe
      (event_slot_type_value before.(EventState) eid) before.(IntrState).(intNesting) =
      Some (result, code) /\ error = encode_os_err_code code) &&
    mutex_del_runtime_entry source_env external platform sg original mask before) ||
  (EX acquired checkpoint request,
    coq_prop (mutex_del_parent_prefix_ok pe before eid /\
      mutex_owner_source_history sg before acquired /\
      mutex_del_parent_critical_observation sg eid option result error request acquired checkpoint) &&
    mutex_del_runtime_return external platform sg original mask) ||
  (EX acquired kind,
    coq_prop (mutex_del_parent_prefix_ok pe before eid /\
      mutex_owner_source_history sg before acquired /\
      mutex_del_runtime_type_observation sg eid acquired kind /\ kind <> 4 /\
      result = pe /\ error = encode_os_err_code OS_ERR_EVENT_TYPE) &&
    mutex_del_runtime_return external platform sg original mask).

Lemma mutex_del_runtime_critical_return : forall external platform sg original mask saved
  before acquired checkpoint pe option eid result error request,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_del_runtime_save_facts sg mask saved before acquired ->
  mutex_del_parent_critical_observation sg eid option result error request acquired checkpoint ->
  mutex_del_runtime_return external platform sg original mask |--
  mutex_del_runtime_post external platform sg original mask before pe option eid result error.
Proof.
  intros external platform sg original mask saved before acquired checkpoint pe option eid result error request
    Hprefix [Hhistory Hrest] Hobservation heap Hpost.
  left; right; exists acquired, checkpoint, request;
    split; [exact (conj Hprefix (conj Hhistory Hobservation))|exact Hpost].
Qed.

Lemma mutex_del_runtime_type_error_return : forall external platform sg original mask saved
  before acquired pe option eid kind,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_del_runtime_save_facts sg mask saved before acquired ->
  mutex_del_runtime_type_observation sg eid acquired kind -> kind <> 4 ->
  mutex_del_runtime_return external platform sg original mask |--
  mutex_del_runtime_post external platform sg original mask before pe option eid pe
    (encode_os_err_code OS_ERR_EVENT_TYPE).
Proof.
  intros external platform sg original mask saved before acquired pe option eid kind
    Hprefix [Hhistory Hrest] Hobservation Hkind heap Hpost.
  right; exists acquired, kind;
    split; [exact (conj Hprefix (conj Hhistory (conj Hobservation
      (conj Hkind (conj eq_refl eq_refl)))))|exact Hpost].
Qed.
End RuntimeContracts.
