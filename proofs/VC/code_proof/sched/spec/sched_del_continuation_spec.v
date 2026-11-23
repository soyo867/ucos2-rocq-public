Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing Del resource instance, split only for OS_Sched's masked
    C prefix. The fragment is re-indexed by the ACTUAL state returned by
    Save/switch/Restore; it is never framed unchanged across those calls. *)
Definition sched_del_continuation_frame sg state : Assertion :=
  coq_prop (mutex_program_selected_reachable sg state /\
    mutex_del_private_types_non_mutex state.(EventState)) &&
  event_private_pool_rep sg state.(EventState).

Definition sched_del_continuation_save_input environment critical saved_local sg call mask state : Assertion :=
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
    unmap_table_rep sg ** sched_del_continuation_frame sg state.

Definition sched_del_continuation_restore_input environment critical saved_local sg call saved acquired released : Assertion :=
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released **
    unmap_table_rep sg ** sched_del_continuation_frame sg released.

Lemma sched_del_continuation_save_input_closed_world : forall environment critical saved_local sg call mask state,
  sched_del_continuation_save_input environment critical saved_local sg call mask state --||--
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key call) call mask state.
Proof.
  intros; unfold sched_del_continuation_save_input.
  rewrite task_tcb_init_continuation_save_input_closed_world.
  unfold kernel_continuation_call_closed, kernel_continuation_inv,
    mutex_del_stack_resources, sched_del_continuation_frame; split; entailer!.
Qed.

Lemma sched_del_continuation_restore_input_masked_world : forall environment critical saved_local sg call saved acquired state,
  sched_del_continuation_restore_input environment critical saved_local sg call saved acquired state --||--
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg
    (task_stack_call_active_key call) call saved acquired state.
Proof.
  intros; unfold sched_del_continuation_restore_input.
  rewrite task_tcb_init_continuation_restore_input_masked_world.
  unfold kernel_continuation_call_masked, kernel_continuation_inv,
    mutex_del_stack_resources, sched_del_continuation_frame; split; entailer!.
Qed.

Lemma sched_del_continuation_frame_prefix : forall sg entry,
  sched_del_continuation_frame sg entry |--
  sched_del_continuation_frame sg (os_sched_prefix_state entry).
Proof.
  intros; unfold sched_del_continuation_frame; Intros_p Hfacts.
  destruct Hfacts as [Hreachable Htypes].
  assert (Hreach : mutex_program_selected_reachable sg (os_sched_prefix_state entry)).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|].
    apply MutexOwnerSourceFrame; reflexivity. }
  change (event_private_pool_rep sg entry.(EventState) |--
    coq_prop (mutex_program_selected_reachable sg (os_sched_prefix_state entry) /\
      mutex_del_private_types_non_mutex entry.(EventState)) &&
    event_private_pool_rep sg entry.(EventState)).
  entailer!.
Qed.

(** C-facing summaries of the unified modular calls. Their normal-return
    identity and indexed resource part is the approved abstract platform
    boundary. The source/cut clauses are C-module R/G obligations. No
    assembly proof, eventual return, or arbitrary environment safety is
    inferred by declaring these predicates. *)
Definition sched_del_continuation_save_output environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      os_sched_call_cut sg returned acquired) &&
    sched_del_continuation_restore_input environment critical saved_local sg returned saved acquired acquired.

Definition sched_del_continuation_restore_output environment critical saved_local sg call saved released : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      (kernel_call_task_source call released -> kernel_call_task_source returned current)) &&
    sched_del_continuation_save_input environment critical saved_local sg returned
      (armv7a_irq_fiq_mask saved) current.

Lemma sched_del_continuation_body_restore_input : forall environment critical saved_local sg call saved acquired entry,
  os_sched_continuation_body_post environment critical saved_local mutex_del_stack_resources
    sg call saved acquired entry |--
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical sg
      entry call returned current /\ UCOS2_state_inv sg current) &&
    sched_del_continuation_restore_input environment critical saved_local sg returned saved acquired current.
Proof.
  intros; unfold os_sched_continuation_body_post; Intros returned current.
  Exists returned current.
  sep_apply_l_atomic (proj2 (sched_del_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired current)).
  unfold sched_del_continuation_restore_input, task_tcb_init_continuation_restore_input,
    UCOS2_inv; entailer!.
Qed.

Lemma sched_del_continuation_restore_output_return : forall environment critical saved_local sg
  original scheduled returned mask saved before entry released,
  task_tcb_init_stack_same_call scheduled original ->
  (kernel_call_task_source original before -> kernel_call_task_source scheduled entry) ->
  (os_sched_requests_switch entry = true -> os_sched_current_storage_binding sg scheduled entry) ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled returned released ->
  interrupt_saved_value mask saved ->
  sched_del_continuation_restore_output environment critical saved_local sg returned saved released |--
  os_sched_continuation_return_post environment saved_local mutex_del_stack_resources sg original mask before.
Proof.
  intros environment critical saved_local sg original scheduled returned mask saved before entry released
    Hscheduled Hsource Hstorage Hbody Hsaved.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  unfold sched_del_continuation_restore_output; Intros final current.
  destruct H as [Hfinal Hcurrent].
  assert (Hsame : task_tcb_init_stack_same_call final original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hcurrent_source : kernel_call_task_source original before -> kernel_call_task_source final current).
  { intro Hinitial; apply Hcurrent.
    eapply os_sched_continuation_c_return_source; eauto. }
  sep_apply_l_atomic (proj1 (sched_del_continuation_save_input_closed_world
    environment critical saved_local sg final (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold os_sched_continuation_return_post; Exists final current; entailer!.
Qed.
