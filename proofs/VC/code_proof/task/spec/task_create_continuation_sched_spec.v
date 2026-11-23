Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same current resource domain is passed across the Scheduler call.
    This is a modular caller contract. Each actual Scheduler return family
    must produce the indexed map; the definition grants no new platform
    guarantee and does not assert total callee coverage. *)
Definition os_sched_continuation_pre environment saved_local resources sg original mask before : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    resources (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key original) original mask before.

Definition os_sched_continuation_return_post environment saved_local resources sg original mask before : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current)) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations)
      resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key returned) returned mask current.

(** The actual C prefix changes the high-ready cache and, on a switching
    path, the counter.  Its current-task fields, ready membership and
    interrupt guards are unchanged.  This transports an already proved
    caller stage; it does not infer readiness from current-task identity. *)
Lemma task_create_sched_prefix_preserves_call_stage : forall call state,
  task_create_call_stage call state ->
  task_create_call_stage call (os_sched_prefix_state state).
Proof.
  intros call state Hstage.
  destruct (os_sched_ready_checkpoint_frame state) as [Hrdy [Hcur [Hprio Hrunning]]].
  unfold task_create_call_stage, task_create_call_origin,
    sched_current_ready_at, os_sched_selection_enabled in *.
  destruct call.(os_sched_call_origin);
    cbn [os_sched_prefix_state replace_SchedS TskState SchedState IntrState] in *;
    repeat rewrite Hrdy; repeat rewrite Hcur; repeat rewrite Hprio;
    repeat rewrite Hrunning; exact Hstage.
Qed.

Lemma task_create_running_stage_ready_nonempty : forall call state,
  task_create_call_stage call state ->
  state.(SchedState).(isRunning) = true ->
  os_sched_selection_enabled state = true ->
  state.(SchedState).(readyList) <> [].
Proof.
  intros call state [Horigin Hstage] Hrunning Hen Hempty.
  destruct call.(os_sched_call_origin).
  - unfold task_create_call_origin in Horigin; congruence.
  - destruct Hstage as [_ [_ [_ Hready]]].
    destruct (Hready Hen) as [node [[_ [_ [_ [Hin _]]]] _]].
    rewrite Hempty in Hin; contradiction.
Qed.

(** The TaskCreate consumer of the proved modular no-switch C call.
    OSRunning is the actual caller's branch guard.  The ready-list input
    needed by the C selector is derived from that caller stage, not added
    as a general Scheduler precondition (Pend may enter with a blocked
    current task).  The exact same prefix endpoint is retained alongside
    the existing public return post.  Platform transition premises denote
    completed Save/Restore calls, not promised future returns. *)
Lemma task_create_continuation_nonswitch_sched_call :
  forall environment critical saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call mask state registers before final_registers acquired saved_heap (frame : Assertion),
  task_create_call_stage call state ->
  state.(SchedState).(isRunning) = true ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_continuation_pre environment saved_local kernel_program_inv sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      task_create_call_stage call (os_sched_prefix_state state) /\
      (os_sched_continuation_pre environment saved_local kernel_program_inv sg
        call mask (os_sched_prefix_state state) ** frame) after /\
      (os_sched_continuation_return_post environment saved_local kernel_program_inv sg
        call mask state ** frame) after).
Proof.
  intros environment critical saved_local arch save restore sg call mask state registers before
    final_registers acquired saved_heap frame Hstage Hrunning Hreturn Hvalid Hmask
    Hnoswitch Hpre Hsave.
  assert (Hnonempty : os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []).
  { eapply task_create_running_stage_ready_nonempty; eassumption. }
  destruct (os_sched_modular_nonswitch_continuation_call
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) critical arch environment.(task_stack_call_continuations)
    save restore (task_create_continuation_local saved_local) sg (task_stack_call_active_key call)
    call mask state registers before final_registers acquired saved_heap frame
    Hreturn Hvalid Hmask Hnoswitch Hnonempty Hpre Hsave)
    as [Hstate [Hsave_run [prefix_heap [Hprefix Hfinish]]]].
  split; [exact Hstate|]. split; [exact Hsave_run|].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmask_after Hrestore_prefix Hrestore_suffix.
  destruct (Hfinish cursor written middle final_cursor after Hr0 Hmask_after Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run Hclosed].
  split; [exact Hrestore_run|].
  split; [apply task_create_sched_prefix_preserves_call_stage; exact Hstage|].
  split; [exact Hclosed|].
  assert (Hpack : os_sched_continuation_pre environment saved_local kernel_program_inv sg
      call mask (os_sched_prefix_state state) ** frame |--
    os_sched_continuation_return_post environment saved_local kernel_program_inv sg
      call mask state ** frame).
  { unfold os_sched_continuation_pre, os_sched_continuation_return_post.
    Exists call (os_sched_prefix_state state).
    assert (Hsource : kernel_call_task_source call state ->
      kernel_call_task_source call (os_sched_prefix_state state))
      by apply os_sched_prefix_preserves_task_source.
    unfold task_tcb_init_stack_same_call; entailer!. }
  exact (Hpack after Hclosed).
Qed.

Lemma task_create_continuation_running_sched_pre : forall environment critical saved_local sg call mask state,
  UCOS2_state_inv sg state ->
  sg.(g_OSRunning) # UChar |-> task_create_stack_running state **
  task_create_continuation_without_running environment critical saved_local sg call mask state **
    unmap_table_rep sg |--
  os_sched_continuation_pre environment saved_local kernel_program_inv sg call mask state.
Proof.
  intros environment critical saved_local sg call mask state Hvalid.
  unfold os_sched_continuation_pre, kernel_continuation_call_closed, kernel_continuation_inv,
    task_create_continuation_without_running, task_create_stack_running,
    task_tcb_init_continuation_capsules.
  rewrite kernel_program_inv_split_unmap, critical_region_outside_without_running_rep,
    UCOS2_inv_split_running; entailer!.
Qed.

Lemma os_sched_continuation_return_post_returns_create : forall environment critical saved_local sg
  original scheduled mask before region args task_return lower old_frame upper,
  task_tcb_init_stack_same_call scheduled original ->
  os_sched_continuation_return_post environment saved_local kernel_program_inv sg scheduled mask before |--
  task_create_continuation_post environment critical saved_local sg region args task_return
    lower old_frame upper original mask 0.
Proof.
  intros environment critical saved_local sg original scheduled mask before region args task_return
    lower old_frame upper Hsame.
  unfold os_sched_continuation_return_post; Intros returned current.
  assert (Hreturned : task_tcb_init_stack_same_call returned original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  sep_apply_l_atomic (task_create_continuation_closed_returns_success environment critical saved_local sg
    original returned mask current region args task_return lower old_frame upper Hreturned).
  entailer!.
Qed.

(** A real final C Restore consumes the current masked owner. The prior
    same-call/source observation describes the already executed body;
    it is not an assumption about every possible future interrupt. *)
Lemma os_sched_continuation_uninterrupted_restore_return : forall environment critical saved_local
  resources arch (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask before resumed saved acquired current cursor heap written middle final_cursor after
  (frame : Assertion),
  task_tcb_init_stack_same_call resumed original ->
  (kernel_call_task_source original before -> kernel_call_task_source resumed current) ->
  armv7a_irq_fiq_mask saved = mask ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    resources (task_create_continuation_local saved_local) critical sg
    (task_stack_call_active_key resumed) resumed saved acquired current ** frame) heap ->
  armv7a_restore_prefix_transition restore cursor heap written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor heap final_cursor after /\
  (os_sched_continuation_return_post environment saved_local resources sg original mask before ** frame) after.
Proof.
  intros environment critical saved_local resources arch restore sg original mask before resumed saved acquired
    current cursor heap written middle final_cursor after frame Hsame Hsource Hsaved Hr0 Hmask Hpre Hprefix Hsuffix.
  destruct (kernel_continuation_call_uninterrupted_restore _ _ _ critical arch
    environment.(task_stack_call_continuations) restore resources (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key resumed) resumed saved acquired current cursor heap written middle
    final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix) as [Hrun [Hreturn Hclosed]].
  rewrite Hsaved in Hclosed; split; [exact Hrun|].
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hpack : P |-- Q) end end.
  { unfold os_sched_continuation_return_post; Exists resumed current; entailer!. }
  exact (Hpack after Hclosed).
Qed.
