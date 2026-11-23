Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_save_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Expose the actual resumed context already owned by the C Restore pre.
    This is an existential view of the same resource, not a new assumption
    that the context still equals the pre-Save stack fragment descriptor. *)
Definition mutex_del_source_restore_at environment critical sg original actual mask saved acquired checkpoint :=
  coq_prop (kernel_stack_call_same_call actual original /\ interrupt_saved_value mask saved /\
    mutex_del_call_stage actual checkpoint) &&
  kernel_stack_call_masked environment.(mutex_del_call_continuations) mutex_del_stack_resources
    critical sg (task_stack_call_active_key original) actual saved acquired checkpoint.

Lemma mutex_del_source_restore_open : forall environment critical sg original mask saved acquired checkpoint,
  mutex_del_source_restore_pre environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical sg original mask saved acquired checkpoint |--
  EX actual, mutex_del_source_restore_at environment critical sg original actual mask saved acquired checkpoint.
Proof.
  intros; unfold mutex_del_source_restore_pre; Intros_p Hstage.
  unfold mutex_del_runtime_restore_pre; Intros selected actual.
  destruct H as [Henv [Hsame [Hsaved ->]]].
  pose proof (mutex_del_same_call_stage original actual checkpoint Hsame Hstage) as Hactual.
  Exists actual; unfold mutex_del_source_restore_at; entailer!.
Qed.

Section CounterSourceCallees.
Context (environment : MutexDelCallEnvironment) (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) =>
      mutex_del_restore_handler_owner environment.(mutex_del_call_platform)
        environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** The current C Save Require is consumed here. The MRS value and every
    later register restoration come from the existing concrete source. *)
Lemma mutex_del_source_save_callee_post : forall critical arch
  (suffix : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  call state mask registers before returned_registers returned acquired resumed
  final_registers final_state after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (mutex_del_source_save_pre environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical sg call mask state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  mutex_del_irq_registers_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_save_entry_address suffix + 4)
    (kernel_save_read_cpsr registers) call state before returned_registers returned acquired resumed ->
  armv7a_save_suffix_transition suffix returned_registers acquired resumed final_registers final_state after ->
  final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  (mutex_del_source_save_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical sg call mask final_registers.(kernel_save_r0) state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros critical arch suffix registers_source call state mask registers before returned_registers returned
    acquired resumed final_registers final_state after frame Hnone Hvalid Hmask Hpre Hirqs Hsuffix.
  unfold mutex_del_source_save_pre in Hpre.
  rewrite <- Hmask in Hpre |- *.
  eapply mutex_del_source_irq_save_post; eassumption.
Qed.

(** Restore's real DSB/MSR -> finite counter handlers -> BX branch consumes
    the exact opened C pre. Neither the old critical frame nor a pre-Save
    private-pool snapshot is framed across this execution. *)
Lemma mutex_del_source_restore_callee_post : forall critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  original actual mask saved acquired checkpoint restore_entry cursor before written released
  returned final resumed final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (mutex_del_source_restore_at environment critical sg original actual mask saved acquired checkpoint **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written released ->
  mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_irq_fiq_mask saved) (restore_entry + 8)
    cursor.(kernel_restore_lr) actual checkpoint released returned final resumed ->
  armv7a_restore_suffix_transition restore written resumed final_cursor after ->
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (mutex_del_source_return environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg original mask **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros critical arch restore original actual mask saved acquired checkpoint restore_entry cursor
    before written released returned final resumed final_cursor after frame Hr0 Hmask Hpre Hprefix Hirqs Hsuffix.
  assert (Hopen : mutex_del_source_restore_at environment critical sg original actual mask saved acquired checkpoint **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (kernel_stack_call_same_call actual original /\ interrupt_saved_value mask saved /\
      mutex_del_call_stage actual checkpoint) &&
    (kernel_stack_call_masked environment.(mutex_del_call_continuations) mutex_del_stack_resources critical
      sg (task_stack_call_active_key original) actual saved acquired checkpoint **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame)))
    by (unfold mutex_del_source_restore_at; entailer!).
  destruct (Hopen before Hpre) as [[Hsame [Hsaved Hstage]] Howned].
  destruct (kernel_stack_call_restore_prefix _ _ _ _ _ environment.(mutex_del_call_continuations)
    restore mutex_del_stack_resources sg (task_stack_call_active_key original) actual saved acquired checkpoint
    cursor before written released _ Hr0 Hmask Howned Hprefix) as [Hwritten [Hmemory Hreleased]].
  destruct (mutex_del_counter_irqs_stage_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg Local local_step normal_return
    handler_contract handler_stack handler_fragments (task_stack_call_active_key original)
    _ _ _ _ _ _ _ _ _ _ Hirqs Hstage Hreleased) as [Hfinal [Hreturned Hresumed]].
  set (word := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hword : written.(kernel_restore_msr_word) = Some word) by (rewrite Hwritten; reflexivity).
  assert (Hword_mask : armv7a_irq_fiq_mask word = armv7a_irq_fiq_mask saved)
    by (unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity).
  rewrite <- Hword_mask in Hresumed.
  assert (Hsuffix_open : kernel_stack_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources sg (task_stack_call_active_key original) returned (armv7a_irq_fiq_mask word) final **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      returned (armv7a_irq_fiq_mask word) **
    (kernel_stack_inv environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
      (task_stack_call_active_key original) final **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame)))
    by (unfold kernel_stack_call_closed; entailer!).
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore returned word written resumed
    final_cursor after _ Hword (Hsuffix_open resumed Hresumed) Hsuffix) as [Hcursor [Hmem Hafter]].
  assert (Hsame_original : kernel_stack_call_same_call returned original).
  { destruct Hsame as [Hi [Ho Hs]]; destruct Hreturned as [Hi' [Ho' Hs']].
    unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hreturn_word : final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr)).
  { rewrite Hcursor, Hwritten; reflexivity. }
  split; [exact Hreturn_word|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold mutex_del_source_return, mutex_del_source_return_at, mutex_del_runtime_return_at;
      Exists returned final environment.
    unfold kernel_stack_call_closed, mutex_del_callsite_environment.
    rewrite Hword_mask, (proj2 Hsaved); entailer!. }
  exact (Hclose after Hafter).
Qed.
End CounterSourceCallees.

(** This whole uninterrupted scheduler path performs the real selector
    writes in the equal-priority branch, as well as both deferred guards.
    Nonempty ready is derived from the C caller's established current stage.
    The branch condition describes this execution; it is not a Del API pre. *)
Lemma mutex_del_source_nonswitch_sched_post : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg call mask state registers before final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (mutex_del_source_sched_pre environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (mutex_del_runtime_return environment environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) sg call mask ** frame) after).
Proof.
  intros environment critical arch save restore sg call mask state registers before final_registers
    acquired saved_heap frame Hnone Hcpsr Hmask Hnoswitch Hpre Hsave.
  set (abi := environment.(mutex_del_call_continuations)).
  set (active := task_stack_call_active_key call).
  assert (Hopen : mutex_del_source_sched_pre environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state ** frame |--
    coq_prop (mutex_del_task_call_stage call state /\ UCOS2_state_inv sg state /\
      mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState) /\
      task_stack_live_coverage state.(TskState) active) &&
    (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      call (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
      (UCOS2_inv sg state ** unmap_table_rep sg ** event_private_pool_rep sg state.(EventState) **
        armv7a_task_stack_continuations abi state.(TskState) state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_source_sched_pre, mutex_del_runtime_entry; Intros selected.
    destruct H0 as [Henv ->].
    unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources.
    rewrite kernel_program_inv_split_unmap.
    cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask.
    unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [[Hstage [Hvalid [Hhistory [Htypes Hcoverage]]]] Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call (kernel_save_read_cpsr registers)
    state before final_registers acquired saved_heap _ Hsaved Howned Hsave)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter_save]]]].
  split; [exact Hstate|]; subst acquired.
  match type of Hafter_save with ?P saved_heap => assert (Hprefix_input : P |--
    UCOS2_inv sg state ** unmap_table_rep sg **
    (critical_region_masked environment.(mutex_del_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
      os_sched_context_resources environment.(mutex_del_call_external) call **
      event_private_pool_rep sg state.(EventState) **
      armv7a_task_stack_continuations abi state.(TskState) state.(TskState).(parkedTaskStacks) ** frame))
    by entailer! end.
  destruct (os_sched_source_nonswitch_prefix_resources sg state _ saved_heap Hnoswitch
    (mutex_del_task_call_stage_ready sg call state Hvalid Hstage) (Hprefix_input saved_heap Hafter_save))
    as [prefix_heap [Hprefix Hafter_prefix]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hcursor_r0 Hcursor_mask Hrestore_prefix Hrestore_suffix.
  assert (Hhistory_after : mutex_program_selected_reachable sg (os_sched_prefix_state state)).
  { eapply mutex_program_source_step_reachable; [exact Hhistory|].
    apply MutexOwnerSourceFrame; reflexivity. }
  match type of Hafter_prefix with ?P prefix_heap => assert (Hrestore_input : P |--
    kernel_stack_call_masked abi mutex_del_stack_resources critical sg active call
      final_registers.(kernel_save_r0) state (os_sched_prefix_state state) ** frame) end.
  { unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
    rewrite kernel_program_inv_split_unmap.
    change ((os_sched_prefix_state state).(TskState)) with state.(TskState).
    change ((os_sched_prefix_state state).(EventState)) with state.(EventState); entailer!. }
  destruct (kernel_stack_call_uninterrupted_restore _ _ _ _ _ abi restore mutex_del_stack_resources sg active
    call final_registers.(kernel_save_r0) state (os_sched_prefix_state state) cursor prefix_heap written middle
    final_cursor after frame Hcursor_r0 Hcursor_mask (Hrestore_input prefix_heap Hafter_prefix)
    Hrestore_prefix Hrestore_suffix) as [Hrun [Hword Hafter]].
  split; [exact Hrun|].
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask)
    by (rewrite Hr0; exact Hmask).
  rewrite Hsaved_mask in Hafter.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_stack_call_restore_post; Intros returned current.
    destruct H as [Htrace [Hi [Ho Hstack]]].
    unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned current environment.
    unfold mutex_del_callsite_environment, kernel_stack_call_same_call, active; entailer!. }
  exact (Hclose after Hafter).
Qed.
