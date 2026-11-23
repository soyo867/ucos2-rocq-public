Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual final Restore of either TCB C return branch, for its
    uninterrupted execution family. The existing platform resource
    theorem is called once; no instruction proof or ABI law is added.

    [Hresult] is the already completed publication/no-free C result.
    [Havailable] is a success-only observation of the TCB body's completed updates,
    not a public input premise, future-return promise or invariant of
    partial interrupt states. Registration/reservation/detach and the
    actual intervening return producers must transport it before this
    cut. The failure buffer and arbitrary caller frame remain owned.

    Together with the existing counter-only IRQ final-return producer,
    this supplies concrete instances of the same full sched-call post.
    It does not establish an arbitrary-handler Restore contract. *)
Lemma task_tcb_init_continuation_restore_uninterrupted_sched_call_post :
  forall environment critical saved_local arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg region args task_return lower upper initial_name invocation origin
    mask initial original result call saved acquired released
    cursor before written_cursor middle final_cursor after (frame : Assertion),
  task_tcb_init_stack_same_call call original ->
  interrupt_saved_value mask saved ->
  task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name invocation origin initial result released ->
  task_tcb_init_stack_source_preserved original initial released ->
  (result = 0 -> kernel_call_stack_available original initial ->
    kernel_call_stack_available call released) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_tcb_init_continuation_restore_input environment critical saved_local
     sg call saved acquired released **
   task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args
     task_return lower upper initial_name invocation origin mask initial original result ** frame) after.
Proof.
  intros environment critical saved_local arch restore sg region args task_return lower upper
    initial_name invocation origin mask initial original result call saved acquired released
    cursor before written_cursor middle final_cursor after frame
    Hsame Hsaved Hresult Hsource Havailable Hr0 Hmask Hpre Hprefix Hsuffix.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (UCOS2_state_inv sg released /\
      task_stack_live_coverage released.(TskState) (task_stack_call_active_key call)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
     os_sched_context_resources environment.(task_stack_call_external) call **
     (UCOS2_inv sg released **
      task_tcb_init_continuation_capsules environment saved_local released **
      task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame))) end.
  { unfold task_tcb_init_continuation_restore_input, UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Howned].
  destruct (armv7a_restore_uninterrupted_transports_owned_execution
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch restore
    sg call saved acquired cursor before written_cursor middle final_cursor after _
    Hr0 Hmask Howned Hprefix Hsuffix) as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hrun|]. split; [exact Hreturn|]. split; [exact Hmemory|].
  rewrite (proj2 Hsaved) in Hafter.
  assert (Hpreserved : task_tcb_init_stack_return_preserved original released released).
  { split; [reflexivity|]. split; [auto|apply task_tcb_init_stack_source_preserved_refl]. }
  assert (Hready : result = 0 -> released.(SchedState).(readyList) <> []).
  { intros ->; eapply task_tcb_init_stack_success_ready; exact Hresult. }
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold task_tcb_init_continuation_sched_call_post; Exists released call released.
    unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
      task_tcb_init_continuation_capsules.
    unfold critical_region_outside; rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running; unfold UCOS2_inv; entailer!. }
  exact (Hclose after Hafter).
Qed.
