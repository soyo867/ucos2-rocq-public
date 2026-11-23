Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_nonswitch_phase_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual OSSemPend scheduling call at Source/os_sem.c:629, using
    the same generic-local input as the fresh canonical annotation.

    The existing platform Save and Restore contracts are composed with
    the proved C prefix. All three no-switch branches retain the actual
    call, wait history and owned map on one heap chain. No map is erased
    to its historical empty-local instance.

    The enabled/equal-priority branch additionally establishes the new
    canonical phase output. Its current-cache binding belongs to this
    actual selector cut. The public phase input does not by itself imply
    that binding. Disabled interrupt/lock branches therefore retain their
    honest resource/history endpoint without asserting waiter readiness.
    No source-family restriction is added to the public OSSemPend input. *)
Lemma sem_pend_continuation_nonswitch_scheduler_phase_source :
  forall environment critical saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original mask initial observed eid timeout waiting call state registers before
    final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (sem_pend_continuation_phase_sched_input
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      sem_pend_schedule_return environment.(task_stack_call_external) critical sg
        call call state (os_sched_prefix_state state) /\
      sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
        waiting call (os_sched_prefix_state state) /\
      (kernel_continuation_call_closed environment.(task_stack_call_continuations)
        kernel_program_inv (task_create_continuation_local saved_local) sg
        (task_stack_call_active_key call) call mask (os_sched_prefix_state state) ** frame) after /\
      (kernel_call_task_source call state ->
        sched_current_consistency state.(TskState) state.(SchedState) ->
        os_sched_selection_enabled state = true ->
        sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
          waiting call (os_sched_prefix_state state) /\
        (sem_pend_continuation_phase_sched_output
          (SemPendWaitPhase original mask initial observed eid timeout waiting)
          environment.(task_stack_call_external) environment.(task_stack_call_platform)
          (Some environment) critical saved_local sg call mask state ** frame) after).
Proof.
  intros environment critical saved_local arch save restore sg original mask initial observed eid timeout
    waiting call state registers before final_registers acquired saved_heap frame
    Hreturn Hcpsr Hmask Hnoswitch Hnonempty Hpre Hsave.
  set (abi := environment.(task_stack_call_continuations)).
  set (local := task_create_continuation_local saved_local).
  set (active := task_stack_call_active_key call).
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
      waiting call state) &&
    (kernel_continuation_call_closed abi kernel_program_inv local sg active call mask state ** frame)) end.
  { cbn [sem_pend_continuation_phase_sched_input sem_pend_continuation_sched_input].
    unfold os_sched_continuation_pre, abi, local, active; entailer!. }
  destruct (Hopen before Hpre) as [Hwait Hclosed].
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hclosed with ?P before => assert (Hexpose : P |--
      coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold kernel_continuation_call_closed, kernel_continuation_inv;
        rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hclosed)). }
  destruct (os_sched_modular_nonswitch_continuation_call
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) critical arch abi save restore local sg active
    call mask state registers before final_registers acquired saved_heap frame
    Hreturn Hcpsr Hmask Hnoswitch Hnonempty Hclosed Hsave)
    as [Hstate [Hsave_run [prefix_heap [Hprefix Hfinish]]]].
  assert (Hwait_after : sem_pend_wait_at (Some environment) critical sg original mask initial observed
    eid timeout waiting call (os_sched_prefix_state state)).
  { eapply sem_pend_wait_at_nonswitch_source; eassumption. }
  assert (Hschedule : sem_pend_schedule_return environment.(task_stack_call_external) critical sg
    call call state (os_sched_prefix_state state)).
  { exists state, (os_sched_prefix_state state); split; [constructor|].
    split; [unfold os_sched_c_return; rewrite Hnoswitch; auto|constructor]. }
  split; [exact Hstate|]. split; [exact Hsave_run|].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Hfinish cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run Hafter].
  split; [exact Hrestore_run|]. split; [exact Hschedule|].
  split; [exact Hwait_after|]. split; [exact Hafter|].
  intros Hsource Hcache Henabled.
  pose proof (sem_pend_enabled_nonswitch_wait_selected environment critical sg original mask initial
    observed eid timeout waiting call state Hwait_after Hvalid Hsource Hcache Henabled Hnoswitch
    (Hnonempty Henabled)) as Hselected.
  split; [exact Hselected|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hpack : P |-- Q) end end.
  { cbn [sem_pend_continuation_phase_sched_output]; Exists call (os_sched_prefix_state state).
    rewrite sem_pend_continuation_save_input_owned.
    unfold abi, local, active.
    rewrite <- (task_tcb_init_continuation_save_input_closed_world environment critical saved_local
      sg call mask (os_sched_prefix_state state)).
    unfold kernel_stack_call_same_call; entailer!. }
  exact (Hpack after Hafter).
Qed.

(** The enabled/equal branch directly consumed by the current canonical
    OS_Sched annotation. The selected waiter may be resumed by Post,
    abort or timeout: no pending-result value is constrained here.

    Save/Restore premises denote the actually completed calls. Current
    source/cache/guard facts refer to this entry, not every future entry
    or an assumed final post. The all-branch theorem above preserves the
    disabled cases separately; this specialization is not whole-callee
    coverage and does not change early-error or nonblocking input domains. *)
Lemma sem_pend_continuation_enabled_nonswitch_sched_call :
  forall environment critical saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original mask initial observed eid timeout waiting call state registers before
    final_registers acquired saved_heap (frame : Assertion),
  kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  os_sched_selection_enabled state = true ->
  os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_continuation_phase_sched_input
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      sem_pend_schedule_return environment.(task_stack_call_external) critical sg
        call call state (os_sched_prefix_state state) /\
      sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
        waiting call (os_sched_prefix_state state) /\
      (sem_pend_continuation_phase_sched_output
        (SemPendWaitPhase original mask initial observed eid timeout waiting)
        environment.(task_stack_call_external) environment.(task_stack_call_platform)
        (Some environment) critical saved_local sg call mask state ** frame) after.
Proof.
  intros environment critical saved_local arch save restore sg original mask initial observed eid timeout
    waiting call state registers before final_registers acquired saved_heap frame
    Hsource Hcache Henabled Hnoswitch Hnonempty Hreturn Hcpsr Hmask Hpre Hsave.
  destruct (sem_pend_continuation_nonswitch_scheduler_phase_source environment critical saved_local arch
    save restore sg original mask initial observed eid timeout waiting call state registers before
    final_registers acquired saved_heap frame Hreturn Hcpsr Hmask Hnoswitch
    (fun _ => Hnonempty) Hpre Hsave)
    as [Hstate [Hsave_run [prefix_heap [Hprefix Hfinish]]]].
  split; [exact Hstate|]. split; [exact Hsave_run|].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Hfinish cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run [Hschedule [Hwait_after [Hworld Hphase]]]].
  split; [exact Hrestore_run|]. split; [exact Hschedule|].
  exact (Hphase Hsource Hcache Henabled).
Qed.
