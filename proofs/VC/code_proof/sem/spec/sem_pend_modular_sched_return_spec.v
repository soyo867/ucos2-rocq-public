Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_stack_equiv_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Real enabled/equal-priority Scheduler return for SemPend. Its public
    phase input supplies the original wait and the current resource world;
    the current source/cache/guard observations belong to this Save cut.
    Readiness is DERIVED from the executed selector, never demanded of the
    earlier blocked waiter. Save/Restore use only their existing local
    contracts, and both registered intervals are the actual zero-step
    intervals of this uninterrupted family.

    The result consumes the C-level Sem return consequence on the same
    call/prefix-state indices. Disabled-guard and switching executions are
    not silently included in this theorem. *)
Lemma sem_pend_modular_nonswitch_schedule_return : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid timeout waiting call state registers before
  final_registers acquired saved_heap (frame : Assertion),
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client environment.(task_stack_call_external).(os_sched_hook_action) ->
  kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  os_sched_selection_enabled state = true -> os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_phase_sched_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      sem_pend_schedule_return environment.(task_stack_call_external) critical sg call call state
        (os_sched_prefix_state state) /\
      (os_sched_prefix_state state).(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
      In call.(os_sched_call_stack).(stackLeaseSlot) (os_sched_prefix_state state).(SchedState).(readyList) /\
      (sem_pend_phase_sched_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
        environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
        critical sg call mask state ** frame) after).
Proof.
  intros environment critical arch save restore sg original mask initial observed eid timeout waiting call state
    registers before final_registers acquired saved_heap frame Hclients Hhook Hsource Hcache Henabled Hnoswitch
    Hnonempty Hreturn Hvalid_cpsr Hmask Hpre Hsave.
  set (abi := environment.(task_stack_call_continuations)).
  set (active := task_stack_call_active_key call).
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
      waiting call state) &&
    (kernel_stack_call_closed abi kernel_program_inv sg active call mask state ** frame)) end.
  { cbn [sem_pend_phase_sched_input sem_pend_stack_sched_input].
    unfold os_sched_stack_pre, abi, active; entailer!. }
  destruct (Hopen before Hpre) as [Hwait Hclosed].
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hclosed with ?P before => assert (Hexpose : P |--
      coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold kernel_stack_call_closed, kernel_stack_inv;
        rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hclosed)). }
  assert (Hgeneric : (kernel_continuation_call_closed abi kernel_program_inv (fun _ => emp)
    sg active call mask state ** frame) before).
  { match type of Hclosed with ?P before => match goal with |- ?Q before => assert (Hconvert : P |-- Q) end end.
    { sep_apply_l_atomic (proj2 (kernel_continuation_call_closed_emp_equiv _ _ _ abi
        kernel_program_inv sg active call mask state)); entailer!. }
    exact (Hconvert before Hclosed). }
  destruct (os_sched_modular_nonswitch_continuation_call _ _ _ critical arch abi save restore
    (fun _ => emp) sg active call mask state registers before final_registers acquired saved_heap frame
    Hreturn Hvalid_cpsr Hmask Hnoswitch (fun _ => Hnonempty) Hgeneric Hsave)
    as [Hstate [Hsave_run [prefix_heap [Hprefix Hrestore]]]].
  destruct (os_sched_nonswitch_current_ready_at sg call state Hvalid Hsource Hcache Henabled Hnoswitch Hnonempty)
    as [node [[Hnode [Hcurrent [Hpriority [Hready Heffective]]]] Hgeneration]].
  assert (Hschedule : sem_pend_schedule_return environment.(task_stack_call_external) critical sg call call state
    (os_sched_prefix_state state)).
  { exists state, (os_sched_prefix_state state); split; [constructor|].
    split; [unfold os_sched_c_return; rewrite Hnoswitch; auto|constructor]. }
  split; [exact Hstate|]. split; [exact Hsave_run|]. exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Hrestore cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run Hafter].
  split; [exact Hrestore_run|]. split; [exact Hschedule|]. split; [exact Hcurrent|]. split; [exact Hready|].
  match type of Hafter with ?P after => assert (Hpack : P |--
    kernel_stack_call_history_restore_post abi kernel_program_inv sg active
      (fun entered entry returned current =>
        sem_pend_schedule_return environment.(task_stack_call_external) critical sg entered returned entry current /\
        current.(SchedState).(curTaskID) = Some entered.(os_sched_call_stack).(stackLeaseSlot) /\
        In entered.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList))
      call mask state ** frame) end.
  { sep_apply_l_atomic (proj1 (kernel_continuation_call_closed_emp_equiv _ _ _ abi
      kernel_program_inv sg active call mask (os_sched_prefix_state state))).
    unfold kernel_stack_call_history_restore_post; Exists call (os_sched_prefix_state state).
    unfold kernel_stack_call_same_call; entailer!. }
  exact ((sem_pend_schedule_return_phase_output environment critical sg original mask initial observed eid timeout
    waiting call state frame Hclients Hhook Hwait) after (Hpack after Hafter)).
Qed.
