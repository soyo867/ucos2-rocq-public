Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_wait_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_wake_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_switch_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_public_return_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The actual next-entry boundary registers the foreign Post invocation
    in the same state/world while retaining the original waiting call.
    Consume the physical entry/Save producer immediately: its EventTaskRdy
    precondition and the observed wait now refer to exactly the same entry. *)
Lemma sem_pend_post_entry_wait_history : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg previous original focus mask state eid event before entered registers
  final_registers acquired after (frame : Assertion)
  public_call wait_mask initial observed waiting_eid timeout wait_start,
  let abi := environment.(task_stack_call_continuations) in
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  sem_pend_wait_at (Some environment) critical sg public_call wait_mask initial observed waiting_eid timeout
    wait_start original state ->
  task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key previous.(os_sched_call_stack))) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  sem_post_lookup state eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_addr sg eid <> 0 -> sem_post_group state event <> 0 -> event_object_layout_prop sg eid ->
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      previous mask ** kernel_program_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry entered
    final_registers acquired after ->
  sem_pend_wait_at (Some environment) critical sg public_call wait_mask initial observed waiting_eid timeout
    wait_start original entry /\
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered /\
  kernel_call_save_uninterrupted_execution arch registers entry entered final_registers acquired after /\
  acquired = entry /\
  UCOS2_state_inv sg entry /\
  uchar_load (event_addr sg eid + OSEventGrp_off) (sem_post_group entry event) after /\
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
  exists tid old,
    event_task_rdy_entry sg entry.(TskState) eid event tid old /\
    (event_task_rdy_pre sg entry.(TskState) eid event tid old 1 0
       (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
       (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     (critical_region_masked environment.(task_stack_call_platform) critical sg
        call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
      os_sched_context_resources environment.(task_stack_call_external) call **
      sem_post_wake_frame sg entry eid tid **
      armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame)) after.
Proof.
  intros environment critical arch boundary save sg previous original focus mask state eid event before entered
    registers final_registers acquired after frame public_call wait_mask initial observed waiting_eid timeout
    wait_start abi call entry Hobserved Hlive Hcoverage Hactive Hlookup Htype Hnonnull Hgroup Hlayout
    Hpre Hboundary Hreturn Hcpsr Hmask Hsave.
  split.
  - destruct Hobserved as [owned [Howned [Hsame [Hwait Hpath]]]]; inversion Howned; subst owned.
    exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hwait|].
    eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceSequentialEntry; [exact Hlive|exact Hboundary].
  - exact (sem_pend_post_entry_waiter_pre environment critical arch boundary save sg previous original
      focus mask state eid event before entered registers final_registers acquired after frame
      Hlive Hcoverage Hactive Hlookup Htype Hnonnull Hgroup Hlayout Hpre Hboundary Hreturn Hcpsr Hmask Hsave).
Qed.

(** Register the actual Post critical effect on this same entry/wake
    pair. The actor must be the registered foreign invocation; neither a
    timer step nor a different task's current state is invented. The
    EventTaskRdy source consumer below supplies this very wake result. *)
Lemma sem_pend_registered_post_wait_source : forall environment critical sg original call mask initial observed
  waiting_eid timeout waiting entry actor eid event tid old priority,
  sem_pend_wait_at (Some environment) critical sg original mask initial observed waiting_eid timeout
    waiting call entry ->
  critical.(critical_region_clients) (sem_pend_post_source_client actor eid) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup entry eid event -> sem_post_group entry event <> 0 ->
  sem_post_wake_result sg eid entry (event_wake_state sg entry eid event tid old PendSem 0 PendOK) priority ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed waiting_eid timeout
    waiting call (event_wake_state sg entry eid event tid old PendSem 0 PendOK).
Proof.
  intros environment critical sg original call mask initial observed waiting_eid timeout waiting entry
    actor eid event tid old priority [owned [Howned [Hsame [Hwait Hpath]]]] Hin Hforeign Hlookup Hgroup Hwake.
  inversion Howned; subst owned.
  pose proof (sem_post_wake_result_critical sg eid entry event
    (event_wake_state sg entry eid event tid old PendSem 0 PendOK) priority Hlookup Hgroup Hwake) as Hpost.
  assert (Hstep : kernel_client_step (sem_pend_post_source_client actor eid) sg entry
    (event_wake_state sg entry eid event tid old PendSem 0 PendOK)).
  { exists (OS_ERR_NONE, true); exact Hpost. }
  assert (Hsource : kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin) entry false
      original.(os_sched_call_origin) (event_wake_state sg entry eid event tid old PendSem 0 PendOK)).
  { eapply KernelResumptionTaskSourceSegment with (stopped1 := false) (stopped2 := false).
    - eapply KernelClientTaskSourceStep with (action := sem_pend_post_source_client actor eid)
        (stopped := false).
      + exact Hin.
      + cbn [sem_pend_post_source_client kernel_client_actor]; congruence.
      + intros invocation Hnone; discriminate.
      + exact Hstep.
      + eapply TaskExecutionClientFrame; [exact Hstep|].
        unfold event_wake_state, sched_wake_by_status;
          destruct (task_status_is_suspended _); reflexivity.
      + constructor.
    - constructor.
    - constructor. }
  exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hwait|].
  eapply SemPendWaitSourceTrans; [exact Hpath|].
  eapply SemPendWaitSourceClients; [exact Hsource|].
  intros previous Hprevious Hcontinuation.
  destruct (sem_pend_post_critical_projection sg eid entry (OS_ERR_NONE, true)
    (event_wake_state sg entry eid event tid old PendSem 0 PendOK)
    original.(os_sched_call_stack).(stackLeaseSlot) previous Hpost Hprevious)
    as [current [Hcurrent Hprojection]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

(** Extend the physical EventTaskRdy -> Restore -> Scheduler Save/selector
    producer with the SAME wait history needed by the existing live-switch
    public-return consumer. The Post action is certified/registered for this
    foreign caller. Other actors or unconnected entry registrations retain
    their own obligations; the public SemPend Require remains unchanged. *)
Lemma sem_pend_post_wake_observed_sched_prefix : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry eid event tid old priority call saved original suspended waiting waiting_event
  before (frame : Assertion) cursor written middle final_cursor released
  registers final_registers acquired saved_heap public_call mask initial observed timeout wait_start,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed waiting_event timeout
    wait_start original entry ->
  critical.(critical_region_clients) (sem_pend_post_source_client call.(os_sched_call_invocation) eid) ->
  call.(os_sched_call_invocation) <> public_call.(os_sched_call_invocation) ->
  sem_post_group entry event <> 0 ->
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation waiting_event original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  os_sched_requests_switch checkpoint = true -> checkpoint.(SchedState).(readyList) <> [] ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) call **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) before ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released
    final_registers acquired saved_heap ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  kernel_call_save_uninterrupted_execution arch registers checkpoint released final_registers acquired saved_heap /\
  acquired = checkpoint /\
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed waiting_event timeout
    wait_start original checkpoint /\
  exists prefix_heap current,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    sched_high_ready_consistency selected.(TskState) selected.(SchedState) /\
    selected.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    sem_pend_wait_continuation waiting_event original.(os_sched_call_stack).(stackLeaseGeneration) current /\
    task_invocation_active selected.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
    task_saved_pointer_at selected original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) /\
    selected.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
      Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) /\
    (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
       environment.(task_stack_call_port) abi sg call focus selected ** unmap_table_rep sg **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) checkpoint ** frame)) prefix_heap.
Proof.
  intros environment critical arch restore save sg entry eid event tid old priority call saved original
    suspended waiting waiting_event before frame cursor written middle final_cursor released registers
    final_registers acquired saved_heap public_call mask initial observed timeout wait_start abi focus checkpoint selected
    Hobserved Hin Hforeign Hgroup Hvalid Hlookup Htype Hentry Hcoverage Hwaiting Hwait Hactive Hpointer Hparked
    Hswitch Hnonempty Hpre Hr0 Hmask Hprefix Hsuffix Hreturn Hcpsr Hnextmask Hsave.
  destruct (sem_pend_post_wake_sched_prefix environment critical arch restore save sg entry eid event tid old
    priority call saved original suspended waiting waiting_event before frame cursor written middle final_cursor
    released registers final_registers acquired saved_heap Hvalid Hlookup Htype Hentry Hcoverage Hwaiting Hwait
    Hactive Hpointer Hparked Hswitch Hnonempty Hpre Hr0 Hmask Hprefix Hsuffix Hreturn Hcpsr Hnextmask Hsave)
    as [Hrestore_run [Hsave_run [Hacquired Hselected]]].
  assert (Hobserved_after : sem_pend_wait_at (Some environment) critical sg public_call mask initial observed
    waiting_event timeout wait_start original checkpoint).
  { pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
    assert (Hkind : event_type_to_pend_type event.(eventType) = Some PendSem)
      by (rewrite Htype; reflexivity).
    destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
    inversion Hhead; subst head.
    destruct (event_wake_head sg entry eid event tid tail PendSem 0 PendOK Hvalid Hlookup Hkind Hlist)
      as [found [Hfound [Hwake Hrest]]].
    assert (found = old) by congruence; subst found.
    eapply sem_pend_registered_post_wait_source;
      [exact Hobserved|exact Hin|exact Hforeign|exact Hlookup|exact Hgroup|exact Hwake]. }
  split; [exact Hrestore_run|]. split; [exact Hsave_run|]. split; [exact Hacquired|].
  split; [exact Hobserved_after|]. exact Hselected.
Qed.

(** The same sequential entry and registered Post wake now feed the actual
    selector/switch -> original second Save -> result/cleanup -> public
    return consumer. No caller-supplied wait history at the wake checkpoint
    remains. The ordinary-entry and EventTaskRdy producers above establish
    the matching physical cuts; this finite family retains their source
    boundary and exact event/state endpoints. *)
Lemma sem_pend_post_entry_public_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  sg post_start previous post_event post_tid post_old post_priority post_heap entered_heap
  node old_sp cpsr registers lr prefix suffix first old_words publication
  original suspended original_saved entry eid waiting perr before (frame : Assertion)
  public_call mask initial observed pevent timeout wait_start selector_heap X,
  let context := kernel_sequential_call previous post_start.(TskState).(taskLifecycle).(taskNextInvocation) in
  let post_entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) post_start.(TskState)) post_start in
  let scheduler_entry := event_wake_state sg post_entry eid post_event post_tid post_old PendSem 0 PendOK in
  let state := os_sched_prefix_state scheduler_entry in
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  interrupt_saved_value mask original_saved ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg public_call pevent timeout)) sem_query_observe_error) X ->
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    wait_start original post_start ->
  task_invocation_origin_live post_start.(TskState) previous.(os_sched_call_origin) ->
  kernel_sequential_call_source boundary previous
    post_start.(TskState).(taskLifecycle).(taskNextInvocation) post_heap entered_heap ->
  critical.(critical_region_clients) (sem_pend_post_source_client context.(os_sched_call_invocation) eid) ->
  context.(os_sched_call_invocation) <> public_call.(os_sched_call_invocation) ->
  sem_post_lookup post_entry eid post_event -> sem_post_group post_entry post_event <> 0 ->
  sem_post_wake_result sg eid post_entry scheduler_entry post_priority ->
  os_sched_source_switch_prefix_execution sg selector_heap before ->
  os_sched_source_live_save_input sg state node context old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  event_object_layout_prop sg eid ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg context focus state **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) entry ** unmap_table_rep sg **
    (perr # UChar |->_ ** frame))) before ->
  let saved := armv7a_task_save_image context old_sp cpsr registers lr fragments in
  let hooked := os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments original.(os_sched_call_stack) hooked in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured heap,
      armv7a_task_capture_transition task_abi context saved stored captured ->
      kernel_heap_execution [] captured heap ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg hooked hooked ->
      task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
      exists installed selected,
        sched_install_heap_fragment sg heap installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored cursor restore_written middle final_cursor returned_heap next_registers final_registers acquired after,
          armv7a_task_restore_transition task_abi context selected installed restored ->
          cursor.(kernel_restore_r0) = original_saved ->
          cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
          next_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr next_registers.(kernel_save_cpsr) ->
          armv7a_irq_fiq_mask next_registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask original_saved ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor returned_heap ->
          armv7a_save_suffix_transition save (kernel_save_read_cpsr next_registers) current returned_heap
            final_registers acquired after ->
          os_sched_source_switch_execution environment.(task_stack_call_external) environment.(task_stack_call_platform)
            environment.(task_stack_call_port) environment.(task_stack_call_continuations) task_abi sg state
            context old_sp cpsr registers lr saved original.(os_sched_call_stack) selected before restored /\
          kernel_call_task_source (armv7a_continuation_resumed_call selected original) current /\
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor returned_heap /\
          kernel_call_save_uninterrupted_execution arch next_registers current returned_heap final_registers acquired after /\
          acquired = current /\
          kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original /\
          final_registers.(kernel_save_r0) = next_registers.(kernel_save_cpsr) /\
          exists returned resumed result_node cleaning clean_node branch_heap cleaned,
              sem_pend_resume_branch_fragment sg resumed eid public_call.(os_sched_call_stack).(stackLeaseSlot) result_node after branch_heap /\
              sem_pend_cleanup_fragment sg perr
                (encode_os_err_code (sem_pend_resume_error (encode_pend_status result_node.(statPend)))) branch_heap cleaned /\
              sem_pend_checkpoint_result (Some environment) critical sg public_call pevent timeout initial
                (encode_os_err_code (sem_pend_resume_error (encode_pend_status result_node.(statPend))))
                (event_pend_cleanup_state sg false cleaning public_call.(os_sched_call_stack).(stackLeaseSlot) clean_node) /\
              kernel_stack_call_same_call returned public_call /\ interrupt_saved_value mask final_registers.(kernel_save_r0) /\
              (task_tcb_init_stack_restore_input environment critical sg returned final_registers.(kernel_save_r0) resumed
                (event_pend_cleanup_state sg false cleaning public_call.(os_sched_call_stack).(stackLeaseSlot) clean_node) **
                unmap_table_rep sg ** perr # UChar |->
                  encode_os_err_code (sem_pend_resume_error (encode_pend_status result_node.(statPend))) ** frame) cleaned /\
              (forall final_start final_written final_middle final_exit final_heap,
                final_start.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
                armv7a_irq_fiq_mask final_start.(kernel_restore_current_cpsr) = 192 ->
                armv7a_restore_prefix_transition restore final_start cleaned final_written final_middle ->
                armv7a_restore_suffix_transition restore final_written final_middle final_exit final_heap ->
                kernel_call_restore_uninterrupted_execution arch final_start cleaned final_exit final_heap /\
                (sem_pend_stack_call_post environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) (Some environment) critical sg public_call mask
                  pevent timeout perr initial X ** frame) final_heap))).

Proof.
  intros environment critical arch task_abi restore save boundary sg post_start previous post_event
    post_tid post_old post_priority post_heap entered_heap node old_sp cpsr registers lr prefix suffix first
    old_words publication original suspended original_saved entry eid waiting perr before frame public_call mask
    initial observed pevent timeout wait_start selector_heap X context post_entry scheduler_entry state abi focus
    fragments Hnonnull Haddress_event Heid Hslot Hordered Horiginal_saved Hexec Hwait_history Hlive Hboundary
    Hin Hforeign Hpost_lookup Hpost_group Hpost_wake Hprefix Hinput Horigin Hbinding Hcall Hslice Hmask
    Hwaiting Hwait Hactive Hpointer Hparked Hselected Hlayout Hpre.
  assert (Hentry_wait : sem_pend_wait_at (Some environment) critical sg public_call mask initial observed
    eid timeout wait_start original post_entry).
  { destruct Hwait_history as [owned [Howned [Hsame [Hinitial Hpath]]]]; inversion Howned; subst owned.
    exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hinitial|].
    eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceSequentialEntry; [exact Hlive|exact Hboundary]. }
  pose proof (sem_pend_registered_post_wait_source environment critical sg public_call original mask initial
    observed eid timeout wait_start post_entry context.(os_sched_call_invocation) eid post_event post_tid post_old
    post_priority Hentry_wait Hin Hforeign Hpost_lookup Hpost_group Hpost_wake) as Hcheckpoint_wait.
  exact (sem_pend_live_switch_public_return_source environment critical arch task_abi restore save
    sg scheduler_entry node context old_sp cpsr registers lr prefix suffix first old_words publication
    original suspended original_saved entry eid waiting perr before frame public_call mask initial observed pevent
    timeout wait_start selector_heap X Hnonnull Haddress_event Heid Hslot Hordered Horiginal_saved Hexec
    Hcheckpoint_wait Hprefix Hinput Horigin Hbinding Hcall Hslice Hmask Hwaiting Hwait Hactive Hpointer Hparked
    Hselected Hlayout Hpre).
Qed.
