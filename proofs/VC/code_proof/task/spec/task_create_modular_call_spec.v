Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consume the actual OS_TCBInit C post for a running-task caller.  The
    caller's entry source is transported by the already stated callee
    post, including its final Restore; no platform instruction expansion
    is needed.  This does not infer readiness or a taken-key observation.
    Boot and early-error paths use their existing contracts separately. *)
Lemma task_create_modular_tcb_success_sched_input :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial,
  kernel_call_task_source original initial ->
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original 0 ** unmap_table_rep sg |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      kernel_call_task_source returned current) &&
    os_sched_continuation_pre environment saved_local kernel_program_inv sg returned mask current.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial Hinitial.
  sep_apply_l_atomic (task_create_continuation_tcb_success_source environment critical saved_local
    sg region args task_return lower upper initial_name invocation origin original mask initial).
  Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hpreserved : task_tcb_init_stack_source_preserved original initial current) by tauto.
  assert (Hsource : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original current Hsame)).
    apply Hpreserved; exact Hinitial. }
  Exists returned current.
  unfold os_sched_continuation_pre.
  sep_apply_l_atomic (proj1 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned mask current)).
  entailer!.
Qed.

(** C-level consumer after the ACTUAL Scheduler Save has returned.  Its
    input is the current masked contract, not a guessed future acquired
    state. Only selector nonemptiness is needed when the source guards
    enable selection. A successful publication or a real returned selector
    supplies that fact; the outgoing caller need not be ready. All switch and
    no-switch C branches are covered by the existing modular prefix proof.

    The endpoint is precisely the next OSCtxSw/Restore call boundary.  No
    claim here upgrades a weak Save output or supplies the
    subsequent platform call's postcondition. *)
Lemma task_create_modular_sched_prefix :
  forall environment critical saved_local sg call saved acquired state before (frame : Assertion),
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (task_tcb_init_continuation_restore_input environment critical saved_local sg
     call saved acquired state ** unmap_table_rep sg ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg state before after /\
    (os_sched_requests_switch state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (task_tcb_init_continuation_restore_input environment critical saved_local sg
       call saved acquired (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros environment critical saved_local sg call saved acquired state before frame Hnonempty Hpre.
  assert (Hopen :
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      call saved acquired state ** unmap_table_rep sg ** frame |--
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_inv (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key call) call saved acquired state ** frame).
  { sep_apply_l_atomic (proj1 (task_tcb_init_continuation_restore_input_masked_world
      environment critical saved_local sg call saved acquired state)); entailer!. }
  destruct (os_sched_modular_prefix_continuation_resources
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    (task_create_continuation_local saved_local) critical sg (task_stack_call_active_key call)
    call saved acquired state before frame Hnonempty (Hopen before Hpre))
    as [after [Hprefix [Hhigh Hmasked]]].
  exists after; split; [exact Hprefix|].
  split; [exact Hhigh|].
  assert (Hclose :
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_inv (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key call) call saved acquired (os_sched_prefix_state state) ** frame |--
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      call saved acquired (os_sched_prefix_state state) ** unmap_table_rep sg ** frame).
  { sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
      environment critical saved_local sg call saved acquired (os_sched_prefix_state state))); entailer!. }
  exact (Hclose after Hmasked).
Qed.
