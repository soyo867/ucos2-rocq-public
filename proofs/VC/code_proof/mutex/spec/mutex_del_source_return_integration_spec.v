Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_callee_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_save_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Section SchedulerCounterIRQs.
Context (environment : MutexDelCallEnvironment) (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** The actual Del Scheduler call has two independent finite IRQ intervals:
    Save's MRS+4 interval and Restore's MSR+8 interval. The existing registered
    counter-handler sources establish each interval's current world and call
    identity. Scheduler guards and selector bytes are evaluated at [acquired],
    after the first interval; no property of the old entry substitutes for it.

    All three C no-switch branches are included (nonzero interrupt nesting,
    nonzero lock nesting, or equal selected/current priority bytes). Readiness
    comes from the caller's established stage when selection is enabled.
    The frame is returned by each actual IRQ proof, not carried across an IRQ
    by a local C frame rule. The conclusion is the current canonical Scheduler
    Ensure consumed by OSMutexDel; no caller/manual target is changed here. *)
Lemma mutex_del_nonswitch_sched_counter_irqs_source : forall critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  call mask state registers before saved_registers saved_call acquired resumed
  final_registers final_state saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (mutex_del_source_sched_pre environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  mutex_del_irq_registers_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_save_entry_address save + 4)
    (kernel_save_read_cpsr registers) call state before saved_registers saved_call acquired resumed ->
  armv7a_save_suffix_transition save saved_registers acquired resumed final_registers final_state saved_heap ->
  os_sched_requests_switch acquired = false ->
  final_state = acquired /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall restore_entry cursor written released returned current irq_heap final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written released ->
      mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
        environment.(mutex_del_call_continuations) sg Local local_step normal_return
        handler_stack handler_fragments (armv7a_irq_fiq_mask final_registers.(kernel_save_r0))
        (restore_entry + 8) cursor.(kernel_restore_lr) saved_call (os_sched_prefix_state acquired)
        released returned current irq_heap ->
      armv7a_restore_suffix_transition restore written irq_heap final_cursor after ->
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (mutex_del_runtime_return environment environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) sg call mask **
       (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after).
Proof.
  intros critical arch save restore registers_source call mask state registers before saved_registers
    saved_call acquired resumed final_registers final_state saved_heap frame
    Hnone Hvalid_sr Hmask Hpre Hsave_irqs Hsave_suffix Hnoswitch.
  set (abi := environment.(mutex_del_call_continuations)).
  set (active := task_stack_call_active_key call).
  assert (Hopen : mutex_del_source_sched_pre environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (mutex_del_task_call_stage call state) &&
    (kernel_stack_call_closed abi mutex_del_stack_resources sg active call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
     (task_stack_fragments_rep handler_stack handler_fragments ** frame))).
  { unfold mutex_del_source_sched_pre, mutex_del_runtime_entry; Intros selected.
    destruct H0 as [_ ->]. unfold abi, active; rewrite Hmask; entailer!. }
  destruct (Hopen before Hpre) as [Htask Howned].
  pose proof (proj1 (proj1 Htask)) as Horigin.
  assert (Hstage : mutex_del_call_stage call state).
  { unfold mutex_del_call_stage; rewrite Horigin; exact Htask. }
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg
    Local local_step normal_return handler_contract handler_stack handler_fragments critical arch save
    active call state registers before saved_registers saved_call acquired resumed final_registers final_state
    saved_heap frame Hnone Hvalid_sr Howned Hsave_irqs Hsave_suffix)
    as [Hmrs [Hsave_run [Hfinal_state [Hr0 [Hcpsr [Hlr [Hsame [Hevents Hmasked]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg
    Local local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hsave_irqs)
    as [_ [_ [_ Hcounter]]].
  cbn [kernel_save_read_cpsr kernel_save_cpsr] in Hcounter.
  destruct (mutex_del_counter_irqs_stage_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments active _ _ _ _ _ _ _ _ _ _ Hcounter Hstage Howned)
    as [Hacquired_stage [Hsame_acquired Hresumed]].
  assert (Hsaved_origin : saved_call.(os_sched_call_origin) =
    RunningInvocation saved_call.(os_sched_call_stack).(stackLeaseSlot)
      saved_call.(os_sched_call_stack).(stackLeaseGeneration)).
  { rewrite (proj1 (proj2 Hsame)), (proj2 (proj2 Hsame)); exact Horigin. }
  assert (Hacquired_task : mutex_del_task_call_stage saved_call acquired).
  { unfold mutex_del_call_stage in Hacquired_stage; rewrite Hsaved_origin in Hacquired_stage;
      exact Hacquired_stage. }
  assert (Hfacts : kernel_stack_call_masked abi mutex_del_stack_resources critical sg active saved_call
      final_registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (UCOS2_state_inv sg acquired /\ mutex_program_selected_reachable sg acquired /\
      mutex_del_private_types_non_mutex acquired.(EventState) /\
      task_stack_live_coverage acquired.(TskState) active) && TT).
  { unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
    rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
  destruct (proj1 (Hfacts saved_heap Hmasked)) as [Hvalid_acquired [Hhistory [Htypes Hcoverage]]].
  match type of Hmasked with ?P saved_heap => assert (Hprefix_input : P |--
    UCOS2_inv sg acquired ** unmap_table_rep sg **
    (critical_region_masked environment.(mutex_del_call_platform) critical sg
       saved_call.(os_sched_call_invocation) saved_call.(os_sched_call_origin)
       final_registers.(kernel_save_r0) acquired **
     os_sched_context_resources environment.(mutex_del_call_external) saved_call **
     event_private_pool_rep sg acquired.(EventState) **
     armv7a_task_stack_continuations abi acquired.(TskState) acquired.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep handler_stack handler_fragments ** frame)) end.
  { unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (os_sched_source_nonswitch_prefix_resources sg acquired _ saved_heap Hnoswitch
    (mutex_del_task_call_stage_ready sg saved_call acquired Hvalid_acquired Hacquired_task)
    (Hprefix_input saved_heap Hmasked)) as [prefix_heap [Hprefix Hafter_prefix]].
  assert (Hprefix_history : mutex_program_selected_reachable sg (os_sched_prefix_state acquired)).
  { eapply mutex_program_source_step_reachable; [exact Hhistory|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hprefix_stage : mutex_del_call_stage saved_call (os_sched_prefix_state acquired)).
  { unfold mutex_del_call_stage; rewrite Hsaved_origin.
    split.
    - apply os_sched_prefix_preserves_task_source; exact (proj1 Hacquired_task).
    - exact (proj2 Hacquired_task). }
  assert (Hsaved_value : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { split; rewrite Hr0; assumption. }
  match type of Hafter_prefix with ?P prefix_heap => assert (Hrestore_input : P |--
    mutex_del_source_restore_at environment critical sg call saved_call mask
      final_registers.(kernel_save_r0) acquired (os_sched_prefix_state acquired) **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) end.
  { unfold mutex_del_source_restore_at, kernel_stack_call_masked, kernel_stack_inv,
      mutex_del_stack_resources.
    rewrite kernel_program_inv_split_unmap.
    change (os_sched_prefix_state acquired).(TskState) with acquired.(TskState).
    change (os_sched_prefix_state acquired).(EventState) with acquired.(EventState).
    unfold active; entailer!. }
  split; [exact Hfinal_state|]. split; [exact Hr0|]. split; [exact Hlr|].
  exists prefix_heap; split; [exact Hprefix|].
  intros restore_entry cursor written released returned current irq_heap final_cursor after
    Hcursor_r0 Hcursor_mask Hrestore_prefix Hrestore_irqs Hrestore_suffix.
  destruct (mutex_del_source_restore_callee_post environment sg Local local_step normal_return handler_contract
    handler_stack handler_fragments critical arch restore call saved_call mask final_registers.(kernel_save_r0)
    acquired (os_sched_prefix_state acquired) restore_entry cursor prefix_heap written released returned current
    irq_heap final_cursor after frame Hcursor_r0 Hcursor_mask (Hrestore_input prefix_heap Hafter_prefix)
    Hrestore_prefix Hrestore_irqs Hrestore_suffix) as [Hreturn Hsource_return].
  split; [exact Hreturn|].
  match type of Hsource_return with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (mutex_del_source_return_forget environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask); entailer!. }
  exact (Hclose after Hsource_return).
Qed.
End SchedulerCounterIRQs.
