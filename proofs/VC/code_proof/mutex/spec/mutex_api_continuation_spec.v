Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_history_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Retain the source of each completed modular call before the historical
    resource-only return interface forgets it. These relations contain no
    heap entailment, API postcondition, or future-return premise. *)
Definition mutex_api_restore_history environment critical sg original released
  returned current : Prop :=
  exists call,
    kernel_stack_call_same_call call original /\
    sem_pend_modular_call_history
      (mutex_del_runtime_sched_environment environment) critical sg
      call released returned current.

Definition mutex_api_scheduler_history environment critical sg original before
  returned current : Prop :=
  os_sched_del_call_history (mutex_del_runtime_sched_environment environment)
    critical sg original before returned current.

(** [request] is the actual C scheduling flag, not a request that the
    callee eventually return. The return worlds are the actual Restore
    and optional OS_Sched worlds, kept distinct from [checkpoint]. *)
Definition mutex_api_tail_history environment critical sg original checkpoint
  request returned current : Prop :=
  exists restored unmasked,
    mutex_api_restore_history environment critical sg original checkpoint
      restored unmasked /\
    ((request = 0 /\ returned = restored /\ current = unmasked) \/
     (request = 1 /\ mutex_api_scheduler_history environment critical sg
       restored unmasked returned current)).

Lemma mutex_api_restore_history_same_call :
  forall environment critical sg original released returned current,
  mutex_api_restore_history environment critical sg original released returned current ->
  kernel_stack_call_same_call returned original.
Proof.
  intros * [call [[Hi [Ho Hs]] [_ [[Hi' [Ho' Hs']] _]]]].
  unfold kernel_stack_call_same_call; repeat split; congruence.
Qed.

Lemma mutex_api_tail_history_without_schedule :
  forall environment critical sg original checkpoint returned current,
  mutex_api_restore_history environment critical sg original checkpoint returned current ->
  mutex_api_tail_history environment critical sg original checkpoint 0 returned current.
Proof. intros; exists returned, current; split; [assumption|left; auto]. Qed.

Lemma mutex_api_tail_history_with_schedule :
  forall environment critical sg original checkpoint restored unmasked returned current,
  mutex_api_restore_history environment critical sg original checkpoint restored unmasked ->
  mutex_api_scheduler_history environment critical sg restored unmasked returned current ->
  mutex_api_tail_history environment critical sg original checkpoint 1 returned current.
Proof. intros; exists restored, unmasked; split; [assumption|right; auto]. Qed.

Definition mutex_api_restore_post environment external platform critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (mutex_api_restore_history environment critical sg original released returned current) &&
    mutex_del_continuation_return_at environment external platform saved_local
      sg original mask returned current.

Lemma mutex_api_entry_return_at :
  forall environment external platform saved_local sg original mask before,
  mutex_del_continuation_entry environment external platform saved_local sg original mask before |--
  mutex_del_continuation_return_at environment external platform saved_local
    sg original mask original before.
Proof.
  intros; unfold mutex_del_continuation_entry, mutex_del_continuation_return_at.
  Intros selected; Exists selected; unfold kernel_stack_call_same_call; entailer!.
Qed.

Definition mutex_api_scheduler_post environment external platform critical saved_local
  sg original mask before : Assertion :=
  EX returned current,
    coq_prop (mutex_api_scheduler_history environment critical sg original before returned current) &&
    mutex_del_continuation_return_at environment external platform saved_local
      sg original mask returned current.

Definition mutex_api_tail_post environment external platform critical saved_local
  sg original mask checkpoint request : Assertion :=
  EX returned current,
    coq_prop (mutex_api_tail_history environment critical sg original checkpoint request returned current) &&
    mutex_del_continuation_return_at environment external platform saved_local
      sg original mask returned current.

Lemma mutex_api_sched_body_same_call : forall external critical sg entry call returned current,
  os_sched_c_return external critical sg entry call returned current ->
  kernel_stack_call_same_call returned call.
Proof.
  intros * Hbody; unfold os_sched_c_return in Hbody.
  destruct (os_sched_requests_switch entry).
  - destruct Hbody as [installed [Hswitch [Htrace [Hresume [Hi [Ho [Hs Hrest]]]]]]].
    exact (conj Hi (conj Ho Hs)).
  - destruct Hbody as [-> Hstate]; unfold kernel_stack_call_same_call; auto.
Qed.

(** The final Restore post is consumed at its actual current world. Save
    and C-body facts are the already completed, consecutive call cuts. *)
Lemma mutex_api_scheduler_post_from_calls :
  forall environment critical saved_local rely sg original mask before
    entered acquired resumed released,
  sem_pend_modular_call_history (mutex_del_runtime_sched_environment environment)
    critical sg original before entered acquired ->
  os_sched_c_return environment.(mutex_del_call_external) critical sg
    acquired entered resumed released ->
  kernel_call_modular_restore_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local)
    critical rely sg resumed mask released |--
  mutex_api_scheduler_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical saved_local sg original mask before.
Proof.
  intros * Hsave Hbody; unfold kernel_call_modular_restore_post; Intros returned current.
  destruct H as [Htrace [Hnormal Hrely]].
  assert (Hrestore : sem_pend_modular_call_history
    (mutex_del_runtime_sched_environment environment) critical sg resumed released returned current).
  { unfold sem_pend_modular_call_history;
      cbn [mutex_del_runtime_sched_environment task_stack_call_external task_stack_call_port].
    exact (conj Htrace Hnormal). }
  pose proof (mutex_api_sched_body_same_call _ _ _ _ _ _ _ Hbody) as Hbody_same.
  assert (Hsame : kernel_stack_call_same_call returned original).
  { destruct Hsave as [_ [[Hi [Ho Hs]] _]],
      Hbody_same as [Hi' [Ho' Hs']], Hnormal as [[Hi'' [Ho'' Hs'']] _].
    unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hhistory : mutex_api_scheduler_history environment critical sg original before returned current).
  { exists entered, acquired, resumed, released; auto. }
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
  unfold mutex_api_scheduler_post, mutex_del_continuation_return_at.
  Exists returned current environment; rewrite Hactive.
  unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_api_modular_restore_post :
  forall environment critical saved_local rely sg original call mask released,
  kernel_stack_call_same_call call original ->
  kernel_call_modular_restore_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local)
    critical rely sg call mask released |--
  mutex_api_restore_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical saved_local sg original mask released.
Proof.
  intros * Hcall; unfold kernel_call_modular_restore_post; Intros returned current.
  destruct H as [Htrace [Hnormal Hrely]].
  assert (Hsame : kernel_stack_call_same_call returned original).
  { destruct Hcall as [Hi [Ho Hs]], Hnormal as [[Hi' [Ho' Hs']] Hnormal].
    unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hhistory : mutex_api_restore_history environment critical sg original released returned current).
  { exists call; split; [exact Hcall|].
    unfold sem_pend_modular_call_history;
      cbn [mutex_del_runtime_sched_environment task_stack_call_external task_stack_call_port].
    exact (conj Htrace Hnormal). }
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
  unfold mutex_api_restore_post, mutex_del_continuation_return_at.
  Exists returned current environment; rewrite Hactive.
  unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_api_restore_post_forget :
  forall environment external platform critical saved_local sg original mask released,
  mutex_api_restore_post environment external platform critical saved_local sg original mask released |--
  mutex_del_continuation_return environment external platform saved_local sg original mask.
Proof.
  intros; unfold mutex_api_restore_post, mutex_del_continuation_return.
  Intros returned current; Exists returned current; entailer!.
Qed.

Lemma mutex_api_restore_post_without_schedule :
  forall environment external platform critical saved_local sg original mask checkpoint,
  mutex_api_restore_post environment external platform critical saved_local sg original mask checkpoint |--
  mutex_api_tail_post environment external platform critical saved_local sg original mask checkpoint 0.
Proof.
  intros; unfold mutex_api_restore_post; Intros returned current.
  unfold mutex_api_tail_post; Exists returned current.
  assert (Htail : mutex_api_tail_history environment critical sg original checkpoint 0 returned current)
    by (apply mutex_api_tail_history_without_schedule; assumption).
  entailer!.
Qed.

Lemma mutex_api_return_at_rebase :
  forall environment external platform saved_local sg original resumed mask returned current,
  kernel_stack_call_same_call resumed original ->
  mutex_del_continuation_return_at environment external platform saved_local
    sg resumed mask returned current |--
  mutex_del_continuation_return_at environment external platform saved_local
    sg original mask returned current.
Proof.
  intros * [Hi [Ho Hs]]; unfold mutex_del_continuation_return_at; Intros selected.
  destruct H as [Henv [[Hi' [Ho' Hs']] Hselected]].
  assert (Hsame : kernel_stack_call_same_call returned original).
  { unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hactive : task_stack_call_active_key resumed = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite Ho; reflexivity. }
  Exists selected; rewrite Hactive; entailer!.
Qed.

Lemma mutex_api_scheduler_post_after_restore :
  forall environment external platform critical saved_local sg original mask checkpoint
    restored unmasked,
  mutex_api_restore_history environment critical sg original checkpoint restored unmasked ->
  mutex_api_scheduler_post environment external platform critical saved_local
    sg restored mask unmasked |--
  mutex_api_tail_post environment external platform critical saved_local
    sg original mask checkpoint 1.
Proof.
  intros * Hrestore; unfold mutex_api_scheduler_post; Intros returned current.
  pose proof (mutex_api_restore_history_same_call _ _ _ _ _ _ _ Hrestore) as Hsame.
  sep_apply_l_atomic (mutex_api_return_at_rebase environment external platform saved_local sg
    original restored mask returned current Hsame).
  unfold mutex_api_tail_post; Exists returned current.
  assert (Htail : mutex_api_tail_history environment critical sg original checkpoint 1 returned current)
    by (eapply mutex_api_tail_history_with_schedule; eassumption).
  entailer!.
Qed.
