Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_del_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A concrete normal-return family, not a guarantee about every registry
    trace.  The already established caller view has a matched interrupt
    entry.  The existing Tick client supplies the actual handler body,
    including its proved application-post sequence.  Its counter and
    running-field frames are consequences of that C semantics.

    [parked] is the existing IRQ-entry endpoint, including the saved-SP
    store and parked map.  The last take only removes the restored key.
    Every other field after the handler is retained.  No premise equates
    the requested final counters with the initial counters.

    For a running KernelCaller, nesting agreement gives initial nesting
    zero, so initially-disabled means locked.  This does not cover an
    interrupted KernelInterrupt or certify arbitrary BSP handler bodies.
    The existing Tick entry protocol also retains its selected-profile
    restriction; this theorem does not silently broaden it. *)
Lemma time_tick_locked_irq_return_cut :
  forall app value counter invocation origin handler sg initial call suspended body,
  let observed := initial.(SchedState).(isRunning) in
  let parked := armv7a_irq_live_parked_state initial call
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) in
  let exited := os_int_exit_counter_state observed body in
  let current := os_int_exit_wrapper_restored_state exited suspended.(armv7a_continuation_stack) in
  UCOS2_state_inv sg parked ->
  kernel_interrupt_nesting_agrees observed (kernel_call_execution_context call) initial.(IntrState) ->
  os_sched_selection_enabled initial = false ->
  kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg parked body ->
  body.(SchedState).(isRunning) = observed /\
  kernel_control_step (KernelEnterInterrupt handler observed)
    (kernel_call_execution_context call) initial.(IntrState)
    (KernelInterrupt handler (kernel_call_execution_context call)) parked.(IntrState) false /\
  kernel_control_step (KernelExitInterrupt observed)
    (KernelInterrupt handler (kernel_call_execution_context call)) body.(IntrState)
    (kernel_call_execution_context call) current.(IntrState) false /\
  current.(IntrState) = initial.(IntrState) /\
  os_sched_selection_enabled current = false /\
  interrupt_exit_requests_schedule body.(SchedState).(isRunning) body.(IntrState) = false.
Proof.
  intros app value counter invocation origin handler sg initial call suspended body
    observed parked exited current Hvalid Hagrees Hdisabled Hbody.
  assert (Hbound : initial.(SchedState).(isRunning) = true ->
    0 <= initial.(IntrState).(intNesting) < 255).
  { intro Hrunning; unfold observed in Hagrees.
    specialize (Hagrees Hrunning).
    cbn [kernel_call_execution_context kernel_interrupt_depth] in Hagrees; lia. }
  assert (Hentry_counters : parked.(IntrState) =
    interrupt_enter_state observed initial.(IntrState)).
  { change ((armv7a_irq_entry_counter_state initial).(IntrState) =
      interrupt_enter_state observed initial.(IntrState)).
    rewrite (armv7a_irq_entry_counter_eq_c_entry initial Hbound); reflexivity. }
  destruct (tmr_del_tick_client_intr_timer_eq app value counter invocation origin sg
    parked body Hbody Hvalid) as [Hbody_counters Htimer].
  assert (Hrunning : body.(SchedState).(isRunning) = observed).
  { etransitivity; [exact (tmr_del_tick_call_running_eq app sg value counter parked tt body
      (proj2 Hbody) Hvalid)|].
    unfold parked, observed, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state.
    rewrite replace_TskS_other_Sched, os_sched_save_current_sp_scheduler_frame.
    unfold armv7a_irq_entry_counter_state.
    destruct initial.(SchedState).(isRunning) eqn:Hrunning_initial;
      [cbn [replace_IntrS SchedState]|]; exact Hrunning_initial. }
  assert (Hlocked : observed = true -> initial.(IntrState).(lockNesting) <> 0).
  { intros Htrue Hzero.
    pose proof (Hagrees Htrue) as Hnesting.
    cbn [kernel_call_execution_context kernel_interrupt_depth] in Hnesting.
    assert (Henabled : os_sched_selection_enabled initial = true).
    { apply os_sched_selection_enabled_iff; split; assumption. }
    congruence. }
  destruct (kernel_borrowed_interrupt_counter_envelope observed
    call.(os_sched_call_invocation) call.(os_sched_call_origin) handler
    initial.(IntrState) Hagrees Hlocked) as [Henter Hexit].
  fold (kernel_call_execution_context call) in Henter, Hexit.
  rewrite <- Hentry_counters in Henter, Hexit.
  rewrite <- Hbody_counters in Hexit.
  destruct (kernel_control_step_deterministic (KernelExitInterrupt observed)
    (KernelInterrupt handler (kernel_call_execution_context call)) body.(IntrState)
    (kernel_call_execution_context call) initial.(IntrState) false
    (kernel_call_execution_context call) (interrupt_exit_state observed body.(IntrState))
    (interrupt_exit_requests_schedule observed body.(IntrState)) Hexit
    (KernelControlExit handler observed (kernel_call_execution_context call) body.(IntrState)))
    as [Hcontext [Hcounters Hschedule]].
  assert (Hcurrent : current.(IntrState) = initial.(IntrState)).
  { change (interrupt_exit_state observed body.(IntrState) = initial.(IntrState)).
    symmetry; exact Hcounters. }
  split; [exact Hrunning|]. split; [exact Henter|]. split.
  - rewrite Hcurrent; exact Hexit.
  - split; [exact Hcurrent|]. split.
    + unfold os_sched_selection_enabled; rewrite Hcurrent; exact Hdisabled.
    + rewrite Hrunning; symmetry; exact Hschedule.
Qed.

(** The C consumer of that matched Tick interval.  The pre-heap is the
    actual handler-body endpoint.  OSIntExit's guarded reads/store produce
    [exited_heap]; the existing take and approved Restore consume that SAME
    heap and selected descriptor, and the already approved Save suffix
    returns the caller's original MRS observation.

    The registered source trace is still supplied by its actual producer
    at the same [initial,current] endpoints.  This theorem adds the C-level
    guard consequence which that flat trace alone does not express.  It
    neither assumes the desired Scheduler cut nor assumes a future return.
    Restore/suffix conclusions are conditional on their actual transitions.

    The live caller/current/parked premises are the existing IRQ take
    interface.  Other saved locals remain owned throughout.  This instance
    covers the established running, locked Tick-interruption family; the
    general nested-ISR and foreign-handler families are separate obligations. *)
Lemma time_tick_locked_irq_sched_save_output :
  forall environment critical saved_local arch
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    app value counter invocation origin sg initial handler suspended body node mask heap
    (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state initial call
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) in
  let exited := os_int_exit_counter_state initial.(SchedState).(isRunning) body in
  let current := os_int_exit_wrapper_restored_state exited suspended.(armv7a_continuation_stack) in
  let local := task_tcb_init_irq_local saved_local suspended in
  UCOS2_state_inv sg initial -> UCOS2_state_inv sg parked ->
  kernel_interrupt_nesting_agrees initial.(SchedState).(isRunning)
    (kernel_call_execution_context call) initial.(IntrState) ->
  os_sched_selection_enabled initial = false ->
  kernel_client_step (tmr_del_tick_client app value counter invocation origin) sg parked body ->
  call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  suspended.(armv7a_continuation_call) = Some call ->
  body.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  body.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  body.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage body.(TskState) None ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    initial false call.(os_sched_call_origin) current ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = mask ->
  interrupt_saved_value mask (nth 0 suspended.(armv7a_continuation_registers) 0) ->
  (UCOS2_inv sg body ** store_parked_continuations
     (kernel_saved_continuation_entry abi body.(TskState) local) body.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame)) heap ->
  exists exited_heap,
    os_int_exit_masked_no_schedule_fragment sg heap exited_heap /\
    kernel_control_step (KernelExitInterrupt initial.(SchedState).(isRunning))
      (KernelInterrupt handler.(os_int_exit_invocation) (kernel_call_execution_context call)) body.(IntrState)
      (kernel_call_execution_context call) current.(IntrState) false /\
    armv7a_continuation_restore_reads suspended exited_heap /\
    (forall restored cursor final_registers acquired after,
      armv7a_restore_transition abi handler suspended exited_heap restored ->
      cursor.(kernel_save_cpsr) = suspended.(armv7a_continuation_cpsr) ->
      cursor.(kernel_save_r0) = nth 0 suspended.(armv7a_continuation_registers) 0 ->
      armv7a_save_suffix_transition suffix cursor current restored final_registers acquired after ->
      acquired = current /\ os_sched_selection_enabled acquired = false /\
      (os_sched_continuation_call_save_output environment critical saved_local sg call mask
         final_registers.(kernel_save_r0) initial ** unmap_table_rep sg **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame) after).
Proof.
  intros environment critical saved_local arch suffix app value counter invocation origin sg
    initial handler suspended body node mask heap frame call abi parked exited current local
    Hinitial Hparked Hagrees Hdisabled Hbody Horigin Hcall Hcurrent Hnode Hgen Hlookup Haddress
    Hcoverage Htrace Hmask Hsaved_word Hpre.
  destruct (time_tick_locked_irq_return_cut app value counter invocation origin
    handler.(os_int_exit_invocation) sg initial call suspended body Hparked Hagrees Hdisabled Hbody)
    as [Hrunning [Henter [Hexit [Hcounters [Hcurrent_disabled Hnoschedule]]]]].
  fold parked exited current in Hrunning, Henter, Hexit, Hcounters, Hcurrent_disabled, Hnoschedule.
  match type of Hpre with ?P heap => assert (Horder : P |-- UCOS2_inv sg body **
    (store_parked_continuations (kernel_saved_continuation_entry abi body.(TskState) local)
       body.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame)))
    by entailer! end.
  destruct (os_int_exit_masked_no_schedule_frame_post sg body _ heap Hnoschedule (Horder heap Hpre))
    as [exited_heap [Hfragment Howned]].
  rewrite Hrunning in Howned; fold exited in Howned.
  assert (Htake_input : (UCOS2_inv sg exited ** store_parked_continuations
    (kernel_saved_continuation_entry abi exited.(TskState) local) exited.(TskState).(parkedTaskStacks) **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame)) exited_heap).
  { match type of Howned with ?P exited_heap => assert (Hassoc : P |--
      UCOS2_inv sg exited ** store_parked_continuations
        (kernel_saved_continuation_entry abi exited.(TskState) local) exited.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
         handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame))
      by entailer! end.
    exact (Hassoc exited_heap Howned). }
  destruct (task_tcb_init_irq_take_resources _ _ _ abi sg exited saved_local suspended call node
    _ exited_heap Hcall Hcurrent Hnode Hgen Hlookup Haddress Hcoverage Htake_input)
    as [Hpointers [Hreads [Hfinal_coverage Htake]]].
  fold current in Hfinal_coverage, Htake.
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { destruct (proj1 Hreads) as [Hlength Hbinding].
    rewrite Hcall in Hbinding; symmetry; exact Hbinding. }
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call).
  { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; auto. }
  assert (Hpreserved : task_tcb_init_stack_source_preserved call initial current).
  { eapply task_tcb_init_stack_registered_source_preserved with (returned := call); try eassumption.
    unfold task_tcb_init_stack_same_call; repeat split; reflexivity. }
  exists exited_heap; split; [exact Hfragment|]. split; [exact Hexit|]. split; [exact Hreads|].
  intros restored cursor final_registers acquired after Hrestore Hcursor_cpsr Hcursor_r0 Hsuffix.
  match type of Htake with ?P exited_heap => assert (Hrestore_input : P |--
    interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
    task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
      suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    (UCOS2_inv sg current ** task_tcb_init_continuation_capsules environment saved_local current **
     unmap_table_rep sg ** frame)) end.
  { unfold task_tcb_init_continuation_capsules; fold abi; entailer!. }
  destruct (armv7a_restore_call_resources _ _ _ abi handler suspended call _ exited_heap restored
    Hcall Hreads (Hrestore_input exited_heap Htake) Hrestore) as [Hrestore_memory Hrestored].
  assert (Hsaved : interrupt_saved_value (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) cursor.(kernel_save_r0)).
  { rewrite Hcursor_cpsr, Hcursor_r0, Hmask; exact Hsaved_word. }
  match type of Hrestored with ?P restored => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) **
    (UCOS2_inv sg current ** task_tcb_init_continuation_capsules environment saved_local current **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) end.
  { rewrite Hcursor_cpsr; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ suffix sg
    (armv7a_continuation_resumed_call suspended call) cursor current restored
    final_registers acquired after _ Hsaved (Hsuffix_input restored Hrestored) Hsuffix)
    as [Hacquired [Hmemory [Hreturn [Hr0 Hafter]]]].
  split; [exact Hacquired|]. split; [rewrite Hacquired; exact Hcurrent_disabled|].
  assert (Hsaved_result : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hr0, Hcursor_r0; exact Hsaved_word. }
  assert (Hcoverage_returned : task_stack_live_coverage current.(TskState)
    (task_stack_call_active_key (armv7a_continuation_resumed_call suspended call))).
  { unfold task_stack_call_active_key, armv7a_continuation_resumed_call;
      cbn [os_sched_call_origin]; rewrite Horigin.
    rewrite Hlease in Hfinal_coverage; exact Hfinal_coverage. }
  match type of Hafter with ?P after => assert (Hpack : P |--
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      (armv7a_continuation_resumed_call suspended call) final_registers.(kernel_save_r0) current current **
    unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame) end.
  { unfold task_tcb_init_continuation_restore_input; entailer!. }
  pose proof (os_sched_disabled_save_call_output environment critical saved_local sg call
    (armv7a_continuation_resumed_call suspended call) mask final_registers.(kernel_save_r0)
    initial current Hsame Hsaved_result Hpreserved Hcurrent_disabled) as Hclose.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hresult : P |-- Q) end end.
  { eapply derivable1_trans; [exact Hpack|]. sep_apply_l_atomic Hclose; entailer!. }
  exact (Hresult after Hafter).
Qed.
