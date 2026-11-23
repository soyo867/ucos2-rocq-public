Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma task_create_runtime_call_input_after_return : forall sg args original before returned after,
  task_create_runtime_call_input args original before ->
  kernel_call_control_rely sg before after ->
  kernel_call_normal_return original before returned after ->
  task_tcb_init_stack_source_preserved original before after ->
  task_create_runtime_call_input args returned after.
Proof.
  intros sg args original before returned after Hadmit Hcontrol Hnormal Hsource
    Hpriority Hnesting Hrunning.
  eapply task_create_runtime_call_after_save; eassumption.
Qed.

(** This is the actual priority reservation write. The current TCB and
    parked stack map are unchanged; no environment or platform fact is
    needed to transport runtime admission through this C operation. *)
Lemma task_create_reserve_preserves_runtime_call_input : forall args owner state observer,
  task_create_runtime_call_input args observer state ->
  task_create_runtime_call_input args observer (task_create_stack_reserved args owner state).
Proof.
  intros args owner state observer Hadmit Hpriority Hnesting Hrunning.
  change (state.(IntrState).(intNesting) = 0) in Hnesting.
  change (state.(SchedState).(isRunning) = true) in Hrunning.
  destruct (Hadmit Hpriority Hnesting Hrunning) as [Hsource Havailable].
  split; [apply task_create_stack_reserve_preserves_call_source; exact Hsource|].
  unfold kernel_call_stack_available in *; destruct observer.(os_sched_call_origin); exact Havailable.
Qed.

(** Consumer of the actual first Save used by OSTaskCreate's annotation.
    The C entry facts retain their existing producer; the new runtime
    observation is derived from the guarded public admission and shared
    normal-return contract, without requiring a ready current task. *)
Lemma task_create_modular_save_entry :
  forall environment critical saved_local sg args initial_name original mask saved before,
  task_create_stack_entry sg args initial_name original before ->
  task_create_runtime_call_input args original before ->
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_create_stack_entry sg args initial_name original acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      task_create_runtime_call_input args returned acquired) &&
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      returned saved acquired acquired.
Proof.
  intros environment critical saved_local sg args initial_name original mask saved before Hentry Hadmit.
  sep_apply_l_atomic (task_tcb_init_modular_save_observation environment critical saved_local
    sg original mask saved before).
  Intros returned acquired.
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    before acquired) by tauto.
  pose proof (task_create_stack_entry_after_call sg args initial_name original
    before acquired Hentry Hhistory) as Hacquired.
  assert (Hvalid : UCOS2_state_inv sg before) by exact (proj1 Hentry).
  assert (Hsource : task_tcb_init_stack_source_preserved original before acquired) by tauto.
  assert (Hruntime : task_create_runtime_call_input args returned acquired).
  { eapply (task_create_runtime_call_input_after_return sg args original before returned acquired);
      [exact Hadmit| | |exact Hsource]; tauto. }
  Exists returned acquired; entailer!.
Qed.
