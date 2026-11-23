Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac_scope.

(** Ordinary later API entry, using the current returned heap rather than
    the initial-task ABI. The source stage supplies current/live/ready;
    the existing invocation counter supplies freshness and no reservation.
    Neither fact comes from the CPU interpretation. Boot and ISR early-error
    stages retain the distinctions of task_create_call_stage. The caller's
    real stack fragments, owned kernel world and other frame survive once.

    This proves the entry cut conditional on KernelSequentialCallABI. It
    does not prove intervening application code, or the remaining complete
    Save/Restore/OS_Sched contracts used by the public C verification. *)
Lemma task_create_sequential_entry_world : forall environment
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  sg args name previous mask state before after (frame : Assertion),
  task_create_call_stage previous state ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before after ->
  (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
     (task_stack_call_active_key previous) previous mask state ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := replace_TskS
    (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (coq_prop (task_create_source_entry sg args name call registered) &&
    (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
       (task_stack_call_active_key call) call mask registered ** frame)) after.
Proof.
  intros environment boundary sg args name previous mask state before after frame
    Hstage Hname Hsource Hbefore call registered.
  assert (Hopen : kernel_stack_call_closed environment.(task_stack_call_continuations)
      kernel_program_inv sg (task_stack_call_active_key previous) previous mask state ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) previous mask **
    (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv sg
       (task_stack_call_active_key previous) state ** frame))
    by (unfold kernel_stack_call_closed; entailer!).
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _
    Hsource (Hopen before Hbefore)) as [Hmemory Hreturned].
  fold call in Hreturned; split; [exact Hmemory|].
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Hregister : P |-- Q) end end.
  { unfold kernel_stack_call_closed, kernel_stack_inv; rewrite !kernel_program_inv_split_unmap.
    Intros.
    assert (Hobserve : UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) && UCOS2_inv sg state)
      by (unfold UCOS2_inv; entailer!).
    sep_apply_l_atomic Hobserve; Intros.
    assert (Hvalid : UCOS2_state_inv sg state) by assumption.
    assert (Horigin : task_create_call_origin state call.(os_sched_call_origin)) by exact (proj1 Hstage).
    assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin))
      by (apply task_create_call_origin_live; exact (proj1 Hstage)).
    pose proof (task_create_registered_stack_entry sg args name state call Hvalid Horigin eq_refl Hname)
      as Hentry.
    change (task_create_stack_entry sg args name call registered) in Hentry.
    assert (Hregistered_stage : task_create_call_stage call registered) by exact Hstage.
    assert (Hentry_source : task_create_source_entry sg args name call registered)
      by exact (conj Hentry Hregistered_stage).
    sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state previous.(os_sched_call_origin) Hlive).
    change (armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      registered.(TskState) registered.(TskState).(parkedTaskStacks)) with
      (armv7a_task_stack_continuations environment.(task_stack_call_continuations)
        state.(TskState) state.(TskState).(parkedTaskStacks)).
    entailer!. }
  exact (Hregister after Hreturned).
Qed.
