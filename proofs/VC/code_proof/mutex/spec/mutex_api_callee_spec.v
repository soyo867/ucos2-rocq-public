Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_modular_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Keep the existing callable resources and stage, and retain the same
    modular Restore source before the old wrapper would erase it. *)
Definition mutex_del_api_restore_source_post environment external platform critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (mutex_api_restore_history environment critical sg original released returned current) &&
    mutex_del_continuation_source_return_at environment external platform saved_local
      sg original mask returned current.

Definition mutex_post_api_restore_source_post environment external platform critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (mutex_api_restore_history environment critical sg original released returned current /\
      mutex_post_api_stage sg returned current /\ kernel_stack_call_same_call returned original) &&
    mutex_del_continuation_entry environment external platform saved_local sg returned mask current.

Lemma mutex_del_api_modular_restore_source_post :
  forall environment critical saved_local rely sg original call mask released,
  kernel_stack_call_same_call call original ->
  mutex_del_call_stage call released -> kernel_call_stack_available call released ->
  (forall after, rely sg released after -> mutex_del_call_stage call released ->
    mutex_del_call_stage call after) ->
  kernel_call_modular_restore_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical rely
    sg call mask released |--
  mutex_del_api_restore_source_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical saved_local sg original mask released.
Proof.
  intros * Hcall Hstage Havailable Hstage_rely.
  unfold kernel_call_modular_restore_post; Intros returned current.
  destruct H as [Htrace [Hnormal Hrely]].
  assert (Hhistory : mutex_api_restore_history environment critical sg original released returned current).
  { exists call; split; [exact Hcall|].
    unfold sem_pend_modular_call_history;
      cbn [mutex_del_runtime_sched_environment task_stack_call_external task_stack_call_port].
    exact (conj Htrace Hnormal). }
  destruct Hnormal as [Hsame Hreturned_available].
  assert (Hsame_original : kernel_stack_call_same_call returned original).
  { destruct Hsame as [Hi [Ho Hs]], Hcall as [Hi' [Ho' Hs']].
    unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hstage' : mutex_del_call_stage returned current).
  { eapply mutex_del_same_call_stage; [exact Hsame|]. apply Hstage_rely; assumption. }
  assert (Havailable' : kernel_call_stack_available returned current)
    by (apply Hreturned_available; exact Havailable).
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame_original)); reflexivity. }
  unfold mutex_del_api_restore_source_post, mutex_del_continuation_source_return_at,
    mutex_del_continuation_return_at.
  Exists returned current environment; rewrite Hactive.
  unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_post_api_modular_restore_source_post :
  forall environment critical saved_local sg original call mask released,
  kernel_stack_call_same_call call original -> UCOS2_state_inv sg released ->
  mutex_post_api_stage sg call released -> kernel_sched_ready_clients critical ->
  kernel_call_modular_restore_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical kernel_call_control_rely
    sg call mask released |--
  mutex_post_api_restore_source_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical saved_local sg original mask released.
Proof.
  intros * Hcall Hvalid [Hsource [Havailable Hready]] Hclients.
  unfold kernel_call_modular_restore_post; Intros returned current.
  destruct H as [Htrace [Hnormal [Hrunning Hintr]]].
  assert (Hhistory : mutex_api_restore_history environment critical sg original released returned current).
  { exists call; split; [exact Hcall|].
    unfold sem_pend_modular_call_history;
      cbn [mutex_del_runtime_sched_environment task_stack_call_external task_stack_call_port].
    exact (conj Htrace Hnormal). }
  destruct Hnormal as [Hsame Havailable_after].
  assert (Hsame_original : kernel_stack_call_same_call returned original).
  { destruct Hsame as [Hi [Ho Hs]], Hcall as [Hi' [Ho' Hs']].
    unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hsource' : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  assert (Hstage' : mutex_post_api_stage sg returned current).
  { split; [exact Hsource'|]. split; [apply Havailable_after; exact Havailable|].
    intros Henabled.
    assert (Hready_before : released.(SchedState).(readyList) <> nil).
    { apply Hready; unfold os_sched_selection_enabled in *; rewrite Hintr in Henabled; exact Henabled. }
    exact (proj2 (kernel_call_registered_rely_preserves_invariant _ _ _ kernel_sched_ready_inv
      sg call returned released current Hclients Htrace (conj Hvalid Hready_before))). }
  unfold mutex_post_api_restore_source_post, mutex_del_continuation_entry.
  Exists returned current environment; unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_del_api_restore_source_post_open :
  forall environment external platform critical saved_local sg original mask released,
  mutex_del_api_restore_source_post environment external platform critical saved_local
    sg original mask released |--
  EX returned current,
    coq_prop (mutex_api_restore_history environment critical sg original released returned current /\
      kernel_stack_call_same_call returned original) &&
    mutex_del_continuation_source_return_at environment external platform saved_local
      sg original mask returned current.
Proof.
  intros; unfold mutex_del_api_restore_source_post; Intros returned current.
  pose proof (mutex_api_restore_history_same_call _ _ _ _ _ _ _ H) as Hsame.
  Exists returned current; entailer!.
Qed.

Lemma mutex_del_api_restore_source_post_return :
  forall environment external platform critical saved_local sg original mask released,
  mutex_del_api_restore_source_post environment external platform critical saved_local
    sg original mask released |--
  mutex_api_restore_post environment external platform critical saved_local sg original mask released.
Proof.
  intros; unfold mutex_del_api_restore_source_post, mutex_api_restore_post.
  Intros returned current; Exists returned current.
  unfold mutex_del_continuation_source_return_at; entailer!.
Qed.

Lemma mutex_post_api_restore_source_post_open :
  forall environment external platform critical saved_local sg original mask released,
  mutex_post_api_restore_source_post environment external platform critical saved_local
    sg original mask released |--
  EX returned current,
    coq_prop (mutex_api_restore_history environment critical sg original released returned current /\
      kernel_stack_call_same_call returned original) &&
    (coq_prop (mutex_post_api_stage sg returned current) &&
      mutex_del_continuation_entry environment external platform saved_local sg returned mask current).
Proof. intros; unfold mutex_post_api_restore_source_post; Intros returned current;
  Exists returned current; entailer!. Qed.

Lemma mutex_post_api_restore_source_post_return :
  forall environment external platform critical saved_local sg original mask released,
  mutex_post_api_restore_source_post environment external platform critical saved_local
    sg original mask released |--
  mutex_api_restore_post environment external platform critical saved_local sg original mask released.
Proof.
  intros; unfold mutex_post_api_restore_source_post; Intros returned current.
  destruct H as [Hhistory [Hstage Hsame]].
  unfold mutex_del_continuation_entry; Intros selected; destruct H as [Henv ->].
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
  unfold mutex_api_restore_post, mutex_del_continuation_return_at.
  Exists returned current environment; rewrite Hactive; entailer!.
Qed.

Lemma mutex_del_api_restore_source_post_without_schedule :
  forall environment external platform critical saved_local sg original mask checkpoint,
  mutex_del_api_restore_source_post environment external platform critical saved_local
    sg original mask checkpoint |--
  mutex_api_tail_post environment external platform critical saved_local
    sg original mask checkpoint 0.
Proof.
  intros; sep_apply_l_atomic (mutex_del_api_restore_source_post_return
    environment external platform critical saved_local sg original mask checkpoint).
  apply mutex_api_restore_post_without_schedule.
Qed.

Lemma mutex_post_api_restore_source_post_without_schedule :
  forall environment external platform critical saved_local sg original mask checkpoint,
  mutex_post_api_restore_source_post environment external platform critical saved_local
    sg original mask checkpoint |--
  mutex_api_tail_post environment external platform critical saved_local
    sg original mask checkpoint 0.
Proof.
  intros; sep_apply_l_atomic (mutex_post_api_restore_source_post_return
    environment external platform critical saved_local sg original mask checkpoint).
  apply mutex_api_restore_post_without_schedule.
Qed.

(** The Scheduler starts at the state returned by this Restore. Its input
    is the existing call precondition; the preceding trace remains pure. *)
Lemma mutex_post_api_restore_source_sched_call :
  forall environment external platform critical saved_local sg original mask checkpoint,
  kernel_tcb_stack_field_layout sg ->
  mutex_post_api_scheduler_link sg critical ->
  mutex_post_api_restore_source_post environment external platform critical saved_local
    sg original mask checkpoint |--
  EX returned current,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\
      mutex_api_restore_history environment critical sg original checkpoint returned current /\
      mutex_post_api_scheduler_link sg critical) &&
    os_sched_continuation_call_pre (mutex_del_runtime_sched_environment environment)
      saved_local mutex_del_stack_resources sg returned mask current.
Proof.
  intros * Hlayout Hlink.
  unfold mutex_post_api_restore_source_post; Intros returned current.
  destruct H as [Hhistory [Hstage Hsame]].
  unfold mutex_del_continuation_entry; Intros selected; destruct H as [Henv ->].
  assert (Hvalid : kernel_continuation_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key returned) returned mask current |--
    coq_prop (UCOS2_state_inv sg current) &&
    kernel_continuation_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key returned) returned mask current).
  { unfold kernel_continuation_call_closed, kernel_continuation_inv,
      mutex_del_stack_resources, kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalid; Intros_p Hstate.
  pose proof (mutex_post_api_stage_call_cut _ _ _ Hlayout Hstate Hstage) as Hcut.
  Exists returned current.
  unfold os_sched_continuation_call_pre, os_sched_continuation_pre;
    cbn [mutex_del_runtime_sched_environment task_stack_call_continuations]; entailer!.
Qed.
