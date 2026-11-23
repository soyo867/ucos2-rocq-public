Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual Del-resource Save summary is an instance of the common
    platform boundary plus the separately supplied, guarded C rely facts.
    In particular no unconditional ready fact is imposed on disabled cuts. *)
Lemma sched_del_modular_save_output : forall environment critical saved_local rely sg original mask saved before,
  UCOS2_state_inv sg before -> kernel_tcb_stack_field_layout sg ->
  (forall after, rely sg before after -> os_sched_selection_enabled after = true ->
    after.(SchedState).(readyList) <> nil) ->
  (forall after, rely sg before after -> os_sched_requests_switch after = true ->
    kernel_call_task_source original before /\ kernel_call_stack_available original before) ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical rely
    sg original mask saved before |--
  sched_del_continuation_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local rely sg original mask saved before Hvalid Hlayout Hready Hsource.
  sep_apply_l_atomic (kernel_call_modular_save_post_guarded_cut _ _ _
    environment.(task_stack_call_continuations) mutex_del_stack_resources
    (task_create_continuation_local saved_local) critical rely sg original mask saved before
    Hvalid Hlayout Hready Hsource).
  Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by
    (unfold kernel_call_normal_return in *; tauto).
  assert (Hcut : os_sched_call_cut sg returned acquired) by tauto.
  destruct Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (sched_del_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired acquired)).
  unfold sched_del_continuation_save_output; Exists returned acquired; entailer!.
Qed.

(** Restore returns the same current Del world. Its source implication is
    the existing registered C source theorem; assembly is used only through
    the unified modular normal-return/resource contract. *)
Lemma sched_del_modular_restore_output : forall environment critical saved_local rely sg call saved released,
  UCOS2_state_inv sg released ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical rely
    sg call (armv7a_irq_fiq_mask saved) released |--
  sched_del_continuation_restore_output environment critical saved_local sg call saved released.
Proof.
  intros environment critical saved_local rely sg call saved released Hvalid.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned call) by
    (unfold kernel_call_normal_return in *; tauto).
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
  sep_apply_l_atomic (proj2 (sched_del_continuation_save_input_closed_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  unfold sched_del_continuation_restore_output; Exists returned current; entailer!.
Qed.
