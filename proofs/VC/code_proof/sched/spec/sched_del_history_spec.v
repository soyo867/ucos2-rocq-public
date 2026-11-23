Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The three consecutive, completed C calls retain their actual states.
    The resource instance and normal-return platform boundary are unchanged. *)
Definition os_sched_del_call_history environment critical sg original before returned current : Prop :=
  exists entered acquired resumed released,
    sem_pend_modular_call_history environment critical sg original before entered acquired /\
    os_sched_c_return environment.(task_stack_call_external) critical sg
      acquired entered resumed released /\
    sem_pend_modular_call_history environment critical sg resumed released returned current.

Definition sched_del_history_save_output environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      os_sched_call_cut sg returned acquired /\
      sem_pend_modular_call_history environment critical sg original before returned acquired) &&
    sched_del_continuation_restore_input environment critical saved_local sg returned saved acquired acquired.

Definition sched_del_history_restore_output environment critical saved_local sg call saved released : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      (kernel_call_task_source call released -> kernel_call_task_source returned current) /\
      sem_pend_modular_call_history environment critical sg call released returned current) &&
    sched_del_continuation_save_input environment critical saved_local sg returned
      (armv7a_irq_fiq_mask saved) current.

Definition sched_del_history_return_post environment critical saved_local sg original mask before : Assertion :=
  EX returned current,
    coq_prop (os_sched_del_call_history environment critical sg original before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current)) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key returned) returned mask current.

Lemma sched_del_history_modular_save_output : forall environment critical saved_local rely sg original mask saved before,
  UCOS2_state_inv sg before -> kernel_tcb_stack_field_layout sg ->
  (forall after, rely sg before after -> os_sched_selection_enabled after = true ->
    after.(SchedState).(readyList) <> nil) ->
  (forall after, rely sg before after -> os_sched_requests_switch after = true ->
    kernel_call_task_source original before /\ kernel_call_stack_available original before) ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical rely
    sg original mask saved before |--
  sched_del_history_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local rely sg original mask saved before Hvalid Hlayout Hready Hsource.
  sep_apply_l_atomic (kernel_call_modular_save_post_guarded_cut _ _ _
    environment.(task_stack_call_continuations) mutex_del_stack_resources
    (task_create_continuation_local saved_local) critical rely sg original mask saved before
    Hvalid Hlayout Hready Hsource).
  Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before returned acquired) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by
    (exact (proj1 Hnormal)).
  assert (Hcut : os_sched_call_cut sg returned acquired) by tauto.
  destruct Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  assert (Hhistory : sem_pend_modular_call_history environment critical sg original before returned acquired).
  { unfold sem_pend_modular_call_history; auto. }
  sep_apply_l_atomic (proj2 (sched_del_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  unfold sched_del_history_save_output; Exists returned acquired; entailer!.
Qed.

Lemma sched_del_history_modular_restore_output : forall environment critical saved_local rely sg call saved released,
  UCOS2_state_inv sg released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical rely
    sg call (armv7a_irq_fiq_mask saved) released |--
  sched_del_history_restore_output environment critical saved_local sg call saved released.
Proof.
  intros environment critical saved_local rely sg call saved released Hvalid.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hnormal : kernel_call_normal_return call released returned current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned call) by (exact (proj1 Hnormal)).
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) released false
    returned.(os_sched_call_origin) current) by tauto.
  assert (Hpreserved : task_tcb_init_stack_source_preserved call released current).
  { eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  assert (Hsource : kernel_call_task_source call released -> kernel_call_task_source returned current).
  { intro Hinitial.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    apply Hpreserved; exact Hinitial. }
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call released returned current).
  { unfold sem_pend_modular_call_history; auto. }
  sep_apply_l_atomic (proj2 (sched_del_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  unfold sched_del_history_restore_output; Exists returned current; entailer!.
Qed.

Lemma sched_del_history_restore_output_return : forall environment critical saved_local sg
  original scheduled returned mask saved before entry released,
  task_tcb_init_stack_same_call scheduled original ->
  (kernel_call_task_source original before -> kernel_call_task_source scheduled entry) ->
  (os_sched_requests_switch entry = true -> os_sched_current_storage_binding sg scheduled entry) ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled returned released ->
  interrupt_saved_value mask saved ->
  sem_pend_modular_call_history environment critical sg original before scheduled entry ->
  sched_del_history_restore_output environment critical saved_local sg returned saved released |--
  sched_del_history_return_post environment critical saved_local sg original mask before.
Proof.
  intros environment critical saved_local sg original scheduled returned mask saved before entry released
    Hscheduled Hsource Hstorage Hbody Hsaved Hsave.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  unfold sched_del_history_restore_output; Intros final current.
  destruct H as [Hfinal [Hcurrent Hrestore]].
  assert (Hsame : task_tcb_init_stack_same_call final original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hcurrent_source : kernel_call_task_source original before -> kernel_call_task_source final current).
  { intro Hinitial; apply Hcurrent.
    eapply os_sched_continuation_c_return_source; eauto. }
  assert (Hhistory : os_sched_del_call_history environment critical sg original before final current).
  { exists scheduled, entry, returned, released; auto. }
  sep_apply_l_atomic (proj1 (sched_del_continuation_save_input_closed_world
    environment critical saved_local sg final (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold sched_del_history_return_post; Exists final current; entailer!.
Qed.

Lemma sched_del_history_return_post_forget : forall environment critical saved_local sg original mask before,
  sched_del_history_return_post environment critical saved_local sg original mask before |--
  os_sched_continuation_return_post environment saved_local mutex_del_stack_resources sg original mask before.
Proof.
  intros; unfold sched_del_history_return_post; Intros returned current.
  unfold os_sched_continuation_return_post; Exists returned current; entailer!; tauto.
Qed.
