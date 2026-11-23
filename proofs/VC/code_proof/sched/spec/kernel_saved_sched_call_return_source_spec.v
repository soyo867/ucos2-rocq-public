Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual TaskRestore producer has returned the saved invocation and
    its own Save/inside pair. OS_Sched's modular C boundary then calls
    OS_CPU_SR_Restore with that local saved word. This later call has its
    own LR; no relation to the prior OSCtxSw LR is asserted.

    The uninterrupted Restore consumes the CURRENT masked world. Its
    source-established call identity/current registration produce the
    existing callable return observation, without requiring a flat trace
    across earlier physical installs. The indexed closed owner is also
    retained for callers, such as Del, whose post observes current stage
    facts. These are two observations of the same after heap, not two
    separating copies of its resources. *)
Lemma kernel_saved_sched_call_return_source : forall environment resources critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original returned entry saved acquired current cursor before written middle final_cursor after
  (frame : Assertion),
  kernel_stack_call_same_call returned original ->
  kernel_call_task_source returned current ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) resources critical sg
    (task_stack_call_active_key original) returned saved acquired current ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_stack_call_closed environment.(task_stack_call_continuations) resources sg
    (task_stack_call_active_key original) returned (armv7a_irq_fiq_mask saved) current ** frame) after /\
  (os_sched_stack_return_post environment resources sg original (armv7a_irq_fiq_mask saved) entry ** frame) after.
Proof.
  intros environment resources critical arch restore sg original returned entry saved acquired current cursor
    before written middle final_cursor after frame Hsame Hsource Hr0 Hmask Hpre Hprefix Hsuffix.
  match type of Hpre with ?P before => assert (Hopen : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) returned **
    (kernel_stack_inv environment.(task_stack_call_continuations) resources sg
      (task_stack_call_active_key original) current ** frame)) end.
  { unfold kernel_stack_call_masked; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg returned saved acquired
    cursor before written middle final_cursor after _ Hr0 Hmask (Hopen before Hpre) Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Howned]]].
  assert (Hclosed : (kernel_stack_call_closed environment.(task_stack_call_continuations) resources sg
    (task_stack_call_active_key original) returned (armv7a_irq_fiq_mask saved) current ** frame) after).
  { match type of Howned with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) by (unfold kernel_stack_call_closed; entailer!) end end.
    exact (Hclose after Howned). }
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hclosed|].
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
  { unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post.
    Exists returned current; entailer!. }
  exact (Hpost after Hclosed).
Qed.
