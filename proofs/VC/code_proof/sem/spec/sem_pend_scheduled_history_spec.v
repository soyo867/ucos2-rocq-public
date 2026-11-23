Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.event Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_selected_acquire_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The original Event observation crosses the concrete IRQ deposit and
    Scheduler installation without treating their Task/SP writes as a flat
    client interval. Parked validity is extracted from the physical world
    produced by IRQ entry; the middle uses that SAME registered source trace.
    The result is consumed by the source acquisition observation below. *)
Lemma sem_pend_scheduled_save_event_trace : forall environment critical sg original
  before sp fragments focus payload parked_heap (parked_frame : Assertion)
  stopped returned_origin entry acquired,
  let parked := armv7a_irq_live_parked_state before original sp fragments in
  (kernel_client_call_stack_world environment.(task_stack_call_continuations)
    sg focus payload parked ** parked_frame) parked_heap ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    parked stopped returned_origin entry ->
  acquired.(EventState) = entry.(EventState) ->
  sem_pend_save_event_trace critical sg original.(os_sched_call_invocation) before acquired.
Proof.
  intros environment critical sg original before sp fragments focus payload parked_heap
    parked_frame stopped returned_origin entry acquired parked Hworld Hsource Hevent.
  assert (Hvalid : UCOS2_state_inv sg parked).
  { assert (Hobserve : kernel_client_call_stack_world environment.(task_stack_call_continuations)
      sg focus payload parked ** parked_frame |-- coq_prop (UCOS2_state_inv sg parked) && TT).
    { unfold kernel_client_call_stack_world, kernel_program_inv; entailer!. }
    exact (proj1 (Hobserve parked_heap Hworld)). }
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource)
    as [Hresources Hcontrol].
  pose proof (kernel_resumption_resource_trace_erases _ _ _ _ _ _ _ Hresources) as Htrace.
  exists parked, entry, stopped; split.
  - unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    destruct before.(SchedState).(isRunning);
      cbn [replace_IntrS TskState replace_TskS EventState];
      destruct (before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot));
      reflexivity.
  - split; [exact Hvalid|]. split; assumption.
Qed.

(** This is the source counterpart of the first protected count read.
    The new history is obtained from the actual Save/Scheduler consumer;
    the original mask observation must still come from the interrupted
    register cursor. It is not inferred merely from a same-call identity. *)
Lemma sem_pend_scheduled_source_acquire_count : forall environment critical sg original returned
  before sp fragments focus payload parked_heap (parked_frame frame : Assertion)
  stopped returned_origin entry acquired mask saved eid observed after,
  let parked := armv7a_irq_live_parked_state before original sp fragments in
  (kernel_client_call_stack_world environment.(task_stack_call_continuations)
    sg focus payload parked ** parked_frame) parked_heap ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    parked stopped returned_origin entry ->
  acquired.(EventState) = entry.(EventState) ->
  kernel_call_save_history environment critical sg original before returned acquired ->
  interrupt_saved_value mask saved ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  mutex_query_lookup before eid observed -> observed.(eventType) = OS_EVENT_TYPE_SEM ->
  (UCOS2_inv sg acquired ** frame) after ->
  exists current,
    sem_pend_acquire_observation environment critical sg original returned
      mask saved before acquired eid observed current /\
    (coq_prop (UCOS2_state_inv sg acquired /\ 0 <= encode_event_cnt_value current <= 65535) &&
      ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
       sem_post_count_frame sg acquired eid current ** frame)) after.
Proof.
  intros environment critical sg original returned before sp fragments focus payload parked_heap
    parked_frame frame stopped returned_origin entry acquired mask saved eid observed after parked
    Hworld Hsource Hevent Hhistory Hsaved Hprotocol Hlookup Htype Hpre.
  pose proof (sem_pend_scheduled_save_event_trace environment critical sg original before sp fragments
    focus payload parked_heap parked_frame stopped returned_origin entry acquired Hworld Hsource Hevent) as Htrace.
  assert (Hvalid : UCOS2_state_inv sg acquired).
  { assert (Hobserve : UCOS2_inv sg acquired ** frame |-- coq_prop (UCOS2_state_inv sg acquired) && TT)
      by (unfold UCOS2_inv; entailer!).
    exact (proj1 (Hobserve after Hpre)). }
  destruct (sem_pend_source_acquire_observation environment critical sg original returned mask saved
    before acquired eid observed Hhistory Htrace Hsaved Hvalid Hprotocol Hlookup Htype)
    as [current Hobservation].
  exists current; split; [exact Hobservation|].
  assert (Hsplit : UCOS2_inv sg acquired ** frame |--
    coq_prop (UCOS2_state_inv sg acquired /\ 0 <= encode_event_cnt_value current <= 65535) &&
      ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
       sem_post_count_frame sg acquired eid current ** frame)).
  { sep_apply_l_atomic (sem_pend_acquire_count_split environment critical sg original returned
      mask saved before acquired eid observed current Hobservation); entailer!. }
  exact (Hsplit after Hpre).
Qed.

(** The concrete Scheduler return produced by
    [sem_pend_scheduler_selected_acquire_source] is recorded as a returning
    first-Save history, then immediately consumed at the real count cell.
    The earlier IRQ deposit and registered heap/state/source traces share
    the Scheduler's actual entry heap.  Current/ready comes from the selected
    post, while the unregistered call fields come from the earlier source.
    This theorem does not identify the old EventState with the current one:
    the lookup is at the Scheduler entry, after the registered client trace.
    Handle preservation from the original SemPend entry remains the separate
    operation-protocol observation. *)
Lemma sem_pend_scheduled_save_history_count : forall environment critical arch Extra
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
    KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
  sg original start handler suspended selected first_registers before irq_input saved_heap
  registry_heap entry_heap entry stopped returned_origin checkpoint
  outgoing old_sp cpsr task_registers lr saved incoming restored
  registers final_registers acquired after node eid event (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original (armv7a_save_entry_address save + 4)
    suspended.(armv7a_continuation_lr) in
  let destination := os_sched_install_context outgoing saved.(armv7a_continuation_fragments) incoming
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      outgoing.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) in
  handler.(os_int_exit_interrupted_call) = original ->
  kernel_call_save_instruction_step arch SaveReadCPSR first_registers start before
    (kernel_save_read_cpsr first_registers) start irq_input ->
  suspended.(armv7a_continuation_pc) = armv7a_save_entry_address save + 4 ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  kernel_heap_execution (armv7a_irq_live_entry_writes sg start
    original.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
    saved_heap registry_heap ->
  kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
    KernelClientHeapClosed entry_heap ->
  kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed
    (armv7a_irq_live_parked_state start original suspended.(armv7a_continuation_sp)
      suspended.(armv7a_continuation_fragments)) KernelClientHeapClosed entry ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    (armv7a_irq_live_parked_state start original suspended.(armv7a_continuation_sp)
      suspended.(armv7a_continuation_fragments)) stopped returned_origin entry ->
  os_sched_source_switch_prefix_execution sg entry_heap checkpoint ->
  os_sched_source_switch_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi
    sg (os_sched_prefix_state entry) outgoing old_sp cpsr task_registers lr saved incoming selected
    checkpoint restored ->
  armv7a_continuation_binding selected ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active destination.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) destination ->
  task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
  registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  mutex_query_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  (os_sched_source_selected_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
    sg focus incoming selected node destination ** frame) restored ->
  armv7a_save_suffix_transition save registers destination restored final_registers acquired after ->
  let returned := armv7a_continuation_resumed_call selected original in
  acquired = destination /\
  kernel_save_after_mrs_execution arch registers destination restored final_registers acquired after /\
  (coq_prop (kernel_call_save_history environment critical sg original start returned acquired /\
     kernel_stack_call_same_call returned original /\
     sem_pend_task_call_stage sg returned acquired /\
     task_stack_live_coverage acquired.(TskState) (Some (task_stack_key returned.(os_sched_call_stack))) /\
     UCOS2_state_inv sg acquired /\ mutex_query_lookup acquired eid event /\
     0 <= encode_event_cnt_value event <= 65535 /\
     (encode_event_cnt_value event = 0 -> event_object_layout_prop sg eid ->
       exists waiting, sem_pend_wait_entry sg acquired eid event
         returned.(os_sched_call_stack).(stackLeaseSlot) waiting /\
         kernel_call_task_source returned acquired /\
         sched_current_consistency acquired.(TskState) acquired.(SchedState))) &&
   (critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin)
      final_registers.(kernel_save_r0) acquired **
    os_sched_context_resources environment.(task_stack_call_external) returned **
    (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event **
    sem_post_count_frame sg acquired eid event **
    armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) **
    frame)) after.
Proof.
  intros environment critical arch Extra save task_abi extra_step extra_effect
    sg original start handler suspended selected first_registers before irq_input saved_heap
    registry_heap entry_heap entry stopped returned_origin checkpoint outgoing old_sp cpsr task_registers
    lr saved incoming restored registers final_registers acquired after node eid event frame abi focus destination
    Hhandler Hmrs Hpc Hdeposit Hentry Hheap_trace Hstate_trace Hsource_trace Hprefix Hswitch Hbinding
    Horigin Hactive Hfields Hkey Hcpsr Hr0 Hlr Hsaved Hlookup Htype Hpre Hsuffix returned.
  assert (Hfocused : armv7a_continuation_focus_binding focus selected).
  { match type of Hpre with ?P restored => assert (Hobserve : P |--
      coq_prop (task_stack_key incoming = armv7a_call_focus_key focus ->
        armv7a_continuation_focus_binding focus selected) && TT) end.
    { unfold os_sched_source_selected_post; Intros.
      entailer!; try tauto; intros ? ?; exact I. }
    exact ((proj1 (Hobserve restored Hpre)) Hkey). }
  assert (Hlease : selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hsame.
    pose proof (proj1 Hfocused) as Hcall.
    change (selected.(armv7a_continuation_call) = Some original) in Hcall.
    rewrite Hcall in Hsame; symmetry; exact Hsame. }
  destruct (sem_pend_selected_source_save_return _ _ _ _ _ abi save sg original
    suspended.(armv7a_continuation_lr) incoming selected node destination registers restored
    final_registers acquired after frame Horigin Hactive Hfields Hkey Hcpsr Hr0 Hlr
    Hsaved Hpre Hsuffix)
    as [Hstate [Hselected_pc [Hreturn [Hvalue [Hexecution [Hstage [Hcoverage Howned]]]]]]].
  assert (Hhistory : kernel_call_save_history environment critical sg original start returned acquired).
  { rewrite Hstate in Hsuffix |- *.
    eapply KernelCallSaveScheduled with (extra_step := extra_step) (extra_effect := extra_effect)
      (registers := first_registers) (handler := handler) (suspended := suspended)
      (task_abi := task_abi) (saved := saved) (selected := selected)
      (resume_registers := registers); eassumption. }
  assert (Hsame : kernel_stack_call_same_call returned original)
    by (eapply kernel_call_save_history_same_call; exact Hhistory).
  assert (Hevents : acquired.(EventState) = entry.(EventState)).
  { rewrite Hstate; unfold destination, os_sched_install_context, os_sched_save_current_sp.
    destruct ((os_sched_prefix_state entry).(TskState).(inUsedTaskStates)
      outgoing.(os_sched_call_stack).(stackLeaseSlot)); reflexivity. }
  pose proof (sem_pend_selected_acquire_count_resources _ _ _ critical abi
    sg returned focus final_registers.(kernel_save_r0) entry acquired eid event frame
    Hevents Hlookup Htype Hstage after Howned) as Hcount.
  split; [exact Hstate|]. split; [exact Hexecution|].
  destruct Hcount as [Hfacts Hmemory]; split.
  - exact (conj Hhistory (conj Hsame (conj Hstage (conj Hcoverage Hfacts)))).
  - exact Hmemory.
Qed.
