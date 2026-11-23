Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** A different task may own the running API call while the earlier caller
    remains parked at [focus]. The existing sequential ABI transports the
    same entire focused map as its disjoint frame. Registration changes
    only the already existing invocation ledger. No new execution law,
    stack owner or focus identity is created. *)
Lemma kernel_sequential_call_register_focused_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (boundary : KernelSequentialCallABI external platform)
  sg previous mask state focus before after (frame : Assertion),
  task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin) ->
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before after ->
  (kernel_call_execution_owned external platform previous mask **
   kernel_program_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  let registered := replace_TskS
    (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform call mask **
   kernel_program_inv sg registered **
   armv7a_task_call_stacks abi registered.(TskState) focus registered.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi boundary sg previous mask state focus before after frame
    Hlive Hsource Hbefore registered call.
  match type of Hbefore with ?P before => assert (Hopen : P |--
    kernel_call_execution_owned external platform previous mask **
    (kernel_program_inv sg state **
     armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))
    by entailer! end.
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _ Hsource (Hopen before Hbefore))
    as [Hmemory Hafter].
  split; [exact Hmemory|]. fold call in Hafter.
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hregister : P |-- Q) end end.
  { rewrite !kernel_program_inv_split_unmap.
    sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state previous.(os_sched_call_origin) Hlive).
    change (armv7a_task_call_stacks abi registered.(TskState) focus
      registered.(TskState).(parkedTaskStacks)) with
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks)).
    entailer!. }
  exact (Hregister after Hafter).
Qed.
