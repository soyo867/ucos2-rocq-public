Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_entry_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_interleaving_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_private_irq_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_foreign_init_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The normalizer supplies actual execution and the strong focused world.
    This is the initial-activation case only. The subsequent API entry is
    the already approved, source-bound application boundary, not an
    inductive permission to relabel arbitrary execution. Its caller-stage
    fields are the existing SemPend ordinary-task protocol. Real byte
    observations and the first Save produce the wait cut used below. *)
Lemma task_create_selected_initial_wait_entry_source : forall environment critical arch
  (initial : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg incoming selected node state pending suspended eid event
  before entered registers final_registers acquired after (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  let previous := kernel_selected_call selected state in
  let registered := kernel_selected_call_state selected state in
  let call := kernel_sequential_call previous registered.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) registered.(TskState)) registered in
  selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments) ->
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  state.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio) ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  task_invocation_active state.(TskState) pending.(os_sched_call_invocation) pending.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  mutex_query_lookup state eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg focus incoming selected node state ** unmap_table_rep sg ** frame) before ->
  kernel_sequential_call_source boundary previous registered.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered ->
  uchar_load sg.(g_OSIntNesting) 0 entered -> uchar_load sg.(g_OSLockNesting) 0 entered ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry entered final_registers acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after -> uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  kernel_call_save_uninterrupted_execution arch registers entry entered final_registers acquired after /\
  acquired = entry /\ os_sched_selection_enabled entry = true /\
  task_tcb_init_call_preserved sg pending.(os_sched_call_invocation) state entry /\
  task_invocation_active entry.(TskState) pending.(os_sched_call_invocation) pending.(os_sched_call_origin) /\
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
  sem_pend_wait_entry sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) node /\
  kernel_call_task_source call entry /\ sched_current_consistency entry.(TskState) entry.(SchedState) /\
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
   os_sched_context_resources environment.(task_stack_call_external) call ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros environment critical arch initial boundary save sg incoming selected node state pending suspended eid event
    before entered registers final_registers acquired after frame abi focus payload previous registered call entry
    Hnone Hinitial Hgeometry Hparked Hrunning Hnonidle Hevent Hmulti Hflag Hactive Hpointer Hlookup Hnonnull Hlayout
    Hpre Hboundary Htype Hint Hlock Hreturn Hcpsr Hmask Hsave Hlow Hhigh.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold os_sched_source_selected_post, UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  pose proof (kernel_selected_call_resources _ _ _ abi initial sg focus payload incoming selected node state
    ltac:(intros _; exact Hinitial) ltac:(intros _; exact Hgeometry) Hparked) as Hnormalize.
  cbv zeta in Hnormalize; fold previous registered in Hnormalize.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (previous.(os_sched_call_stack) = incoming /\
      sched_current_ready_at registered.(TskState) registered.(SchedState) incoming.(stackLeaseSlot) node /\
      node.(taskGeneration) = incoming.(stackLeaseGeneration) /\ kernel_call_task_source previous registered /\
      task_stack_live_coverage registered.(TskState) (Some (task_stack_key previous.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
       previous (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) ** kernel_program_inv sg registered **
     armv7a_task_call_stacks abi registered.(TskState) focus registered.(TskState).(parkedTaskStacks) ** frame)) end.
  { sepcon_assoc_change; sep_apply_l_atomic Hnormalize; unfold kernel_pending_call_world; Intros.
    assert (Hcall_stack : previous.(os_sched_call_stack) = incoming) by tauto.
    assert (Hcall_source : kernel_call_task_source previous registered) by tauto.
    assert (Hcovered : task_stack_live_coverage registered.(TskState)
      (Some (task_stack_key previous.(os_sched_call_stack)))) by (rewrite Hcall_stack; tauto).
    entailer!. }
  destruct (Hopen before Hpre) as [[Hstack [Hready [Hgen [Hsource Hcoverage]]]] Howned].
  assert (Hstage : sem_pend_task_call_stage sg previous registered).
  { unfold sem_pend_task_call_stage; split; [exact Hsource|]. split.
    - unfold registered, kernel_selected_call_state; rewrite Hnone; exact Hrunning.
    - exists node; rewrite Hstack.
      exact (conj Hready (conj Hgen (conj Hnonidle (conj Hevent (conj Hmulti Hflag))))). }
  destruct (kernel_selected_call_preserves_pending_fields sg selected state pending
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hvalid Hactive Hpointer)
    as [Hregistered_active Hregistered_pointer].
  fold registered in Hregistered_active, Hregistered_pointer.
  assert (Hregistered_lookup : mutex_query_lookup registered eid event).
  { unfold registered, kernel_selected_call_state; rewrite Hnone; exact Hlookup. }
  destruct (task_create_foreign_wait_entry_source environment critical arch boundary save sg previous pending
    suspended (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered eid event before entered
    registers final_registers acquired after frame Hstage Hcoverage Hregistered_active Hregistered_pointer
    Hregistered_lookup Hnonnull Hlayout Howned Hboundary Htype Hint Hlock Hreturn Hcpsr Hmask Hsave Hlow Hhigh)
    as [Hrun [Hacquired [Hclear [Henabled [Hentry_active [Hentry_pointer [Hentry_coverage
      [old [Hwait [Hentry_source [Hcache Hafter]]]]]]]]]]].
  fold call entry in Hrun, Hacquired, Henabled, Hentry_active, Hentry_pointer, Hentry_coverage,
    Hwait, Hentry_source, Hcache, Hafter.
  assert (Hold : old = node).
  { pose proof (proj1 Hready) as Hnode; pose proof (proj1 (proj2 (proj2 (proj2 Hwait)))) as Hold.
    change (registered.(TskState).(inUsedTaskStates) previous.(os_sched_call_stack).(stackLeaseSlot) = Some old) in Hold.
    rewrite Hstack, Hnode in Hold; congruence. }
  subst old.
  assert (Hbegin : forall current origin,
    task_invocation_origin_live current.(TskState) origin ->
    task_tcb_init_call_preserved sg pending.(os_sched_call_invocation) current
      (replace_TskS (task_begin_invocation origin current.(TskState)) current)).
  { intros current origin Hlive Hcurrent; split.
    - apply UCOS2_begin_task_invocation_preserves_validity; assumption.
    - split; [reflexivity|]. split; [|reflexivity]. intros caller Hregistered.
      apply task_begin_invocation_preserves_invocation_active; [|exact Hregistered].
      pose proof (proj1 (proj2 Hcurrent)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hhistory : task_tcb_init_call_preserved sg pending.(os_sched_call_invocation) state entry).
  { eapply task_tcb_init_call_preserved_trans with (middle := registered).
    - unfold registered, kernel_selected_call_state; rewrite Hnone; apply Hbegin.
      assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
      { unfold previous, kernel_selected_call in Hstack; rewrite Hnone in Hstack; exact Hstack. }
      rewrite Hlease; exists node; split; [|exact Hgen].
      unfold registered, kernel_selected_call_state in Hready; rewrite Hnone in Hready.
      exact (proj1 Hready).
    - apply Hbegin; exact (proj2 (proj2 (proj1 (proj2 Hsource)))). }
  exact (conj Hrun (conj Hacquired (conj Henabled (conj Hhistory (conj Hentry_active
    (conj Hentry_pointer (conj Hentry_coverage (conj Hwait (conj Hentry_source (conj Hcache Hafter)))))))))).
Qed.

(** This prefix stops BEFORE the foreign task's live stack save.  It
    consumes the actual first-Save wait cut, executes SemPend's stores,
    its Restore, the scheduler Save and C selector.  The next ready task
    is selected by the literal ready-list removal, not a future-return
    hypothesis.  In particular the pending initializer owns no invented
    saved-token/inside pair.  Allocation, name and active-call history are
    proved across these operations and returned with the SAME heap. *)
Lemma task_create_foreign_wait_init_checkpoint : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg context foreign_mask entry eid event tid old timeout tail pending suspended
  (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus pending suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  let node := task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid) in
  sem_pend_wait_entry sg entry eid event tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) = tid :: pending.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some pending ->
  task_invocation_active entry.(TskState) pending.(os_sched_call_invocation) pending.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key pending.(os_sched_call_stack)) =
    Some (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  0 <= timeout < 4294967296 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) foreign_mask entry **
   os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) before ->
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid old timeout before waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = foreign_mask ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask foreign_mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers acquired saved_heap /\
        acquired = waiting /\
        exists prefix_heap,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          checkpoint.(SchedState).(curTaskID) = Some context.(os_sched_call_stack).(stackLeaseSlot) /\
          checkpoint.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
          node.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot) /\
          node.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration) /\
          sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState) /\
          checkpoint.(SchedState).(readyList) <> [] /\
          context.(os_sched_call_stack).(stackLeaseSlot) <> pending.(os_sched_call_stack).(stackLeaseSlot) /\
          task_saved_pointer_at checkpoint suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
          task_tcb_init_call_preserved sg pending.(os_sched_call_invocation) entry checkpoint /\
          (forall outgoing sp,
            os_sched_destination_binding environment.(task_stack_call_external) context outgoing
              (os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot) sp)
              pending.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)) /\
          (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
             environment.(task_stack_call_port) abi sg context focus checkpoint ** unmap_table_rep sg **
           (interrupt_platform_saved environment.(task_stack_call_platform)
              (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
            critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame)) prefix_heap)).
Proof.
  intros environment critical arch save restore task_abi sg context foreign_mask entry eid event tid old timeout tail
    pending suspended frame before abi focus waiting checkpoint node Hentry Hsource Hcache Henabled Hlist Habsent
    Hcoverage Hbinding Hcall Hactive Hpointer Hparked Htimeout Hpre.
  pose proof Hentry as [Hvalid [_ [Hcurrent [Hold _]]]].
  pose proof (proj1 Hsource) as Hcontext_origin.
  assert (Htid : context.(os_sched_call_stack).(stackLeaseSlot) = tid).
  { pose proof (proj2 (proj2 Hsource)) as Hcur.
    unfold task_execution_current in Hcur; rewrite Hcontext_origin in Hcur; congruence. }
  assert (Hdifferent : pending.(os_sched_call_stack).(stackLeaseSlot) <> tid).
  { pose proof (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hvalid))))))) as Hnodup.
    rewrite Hlist in Hnodup; inversion Hnodup as [|? ? Hnot _].
    intro Heq; apply Hnot; left; exact Heq. }
  assert (Hkey_ne : task_stack_key pending.(os_sched_call_stack) <> task_stack_key context.(os_sched_call_stack)).
  { unfold task_stack_key; intro Heq; injection Heq; rewrite Htid; congruence. }
  assert (Hlease : suspended.(armv7a_continuation_stack) = pending.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hbound; rewrite Hcall in Hbound; symmetry; exact Hbound. }
  destruct (task_create_foreign_wait_preserves_pending_call environment critical sg context foreign_mask entry
    eid event tid old timeout pending suspended frame before Hentry Hsource Hcache Hcoverage Hactive
    Hpointer Htimeout Hpre) as [waited [Hstores [Hwaiting_source [Hwaiting_cache [Hcovered
      [Hwaiting_active [Hwaiting_pointer Hwaiting]]]]]]].
  fold abi focus waiting in Hwaiting_source, Hwaiting_cache, Hcovered, Hwaiting_active, Hwaiting_pointer, Hwaiting.
  destruct (task_create_foreign_wait_selects_pending sg entry eid event tid old timeout
    pending.(os_sched_call_stack).(stackLeaseSlot) tail Hentry Hcache Henabled Hlist Hdifferent)
    as [Hready [Hswitch Hselected_tid]].
  fold waiting checkpoint in Hready, Hswitch, Hselected_tid.
  assert (Hnonempty : waiting.(SchedState).(readyList) <> []) by (rewrite Hready; discriminate).
  assert (Hcheckpoint_valid : UCOS2_state_inv sg checkpoint).
  { apply os_sched_ready_checkpoint_preserves_validity.
    exact (sem_pend_wait_entry_preserves_validity sg entry eid event tid old timeout Hentry). }
  assert (Hhistory : task_tcb_init_call_preserved sg pending.(os_sched_call_invocation) entry checkpoint).
  { intros _; split; [exact Hcheckpoint_valid|]. split; [reflexivity|]. split; [|reflexivity].
    intros origin Hlive; unfold checkpoint, os_sched_prefix_state, waiting.
    cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState].
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hlive]. }
  exists waited; split; [exact Hstores|].
  intros cursor written middle final_cursor released Hr0 Hcursor_mask Hrestore_prefix Hrestore_suffix.
  match type of Hwaiting with ?P waited => assert (Hrestore_order : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) foreign_mask entry **
    os_sched_context_resources environment.(task_stack_call_external) context **
    (kernel_program_inv sg waiting ** armv7a_task_call_stacks abi waiting.(TskState) focus
      waiting.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg context foreign_mask entry
    cursor waited written middle final_cursor released _ Hr0 Hcursor_mask (Hrestore_order waited Hwaiting)
    Hrestore_prefix Hrestore_suffix) as [Hrestore_execution [Hreturn_word [Hreleased_memory Hreleased]]].
  split; [exact Hrestore_execution|].
  intros registers final_registers acquired saved_heap Hreturn Hvalid_sr Hsave_mask Hsave.
  assert (Hobserved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid_sr|reflexivity]).
  rewrite <- Hsave_mask in Hreleased.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg context (kernel_save_read_cpsr registers)
    waiting released final_registers acquired saved_heap _ Hobserved Hreleased Hsave)
    as [Hacquired [Hsaved_memory [Hsaved_return [Hsaved_r0 Hmasked]]]].
  split.
  { unfold kernel_call_save_uninterrupted_execution; econstructor.
    - constructor; [exact Hreturn|reflexivity].
    - exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  split; [exact Hacquired|]. subst acquired.
  set (retained := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
    critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame).
  match type of Hmasked with ?P saved_heap => assert (Hprefix_order : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg context focus waiting ** unmap_table_rep sg ** retained) end.
  { unfold os_sched_source_switch_pre, kernel_call_execution_owned, critical_region_masked, retained.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (os_sched_source_switch_prefix_resources _ _ _ abi sg waiting context focus retained saved_heap
    Hswitch Hnonempty (Hprefix_order saved_heap Hmasked)) as [prefix_heap [Hprefix [Hhigh Hprefix_owned]]].
  fold checkpoint in Hhigh, Hprefix_owned.
  assert (Hnode : checkpoint.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { change ((if Z.eqb context.(os_sched_call_stack).(stackLeaseSlot) tid then Some node
      else entry.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot)) = Some node).
    rewrite Htid, Z.eqb_refl; reflexivity. }
  assert (Hid : node.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hlinks.
    destruct Hlinks as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    change (old.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot)); rewrite Htid.
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hold]. apply Hdomain; eauto. }
  assert (Hgen : node.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration)).
  { pose proof (proj2 (proj2 (proj1 (proj2 Hsource)))) as Hlive.
    unfold task_invocation_origin_live in Hlive; rewrite Hcontext_origin in Hlive.
    destruct Hlive as [current [Hlookup Hgeneration]]; rewrite Htid, Hold in Hlookup;
      injection Hlookup as Heq; subst current; exact Hgeneration. }
  assert (Hcur : checkpoint.(SchedState).(curTaskID) = Some context.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj2 (proj2 Hwaiting_source)) as Hcur.
    unfold task_execution_current in Hcur; rewrite Hcontext_origin in Hcur.
    change ((os_sched_ready_checkpoint waiting).(curTaskID) = Some context.(os_sched_call_stack).(stackLeaseSlot)).
    rewrite (proj1 (proj2 (os_sched_ready_checkpoint_frame waiting))); exact Hcur. }
  assert (Hready_checkpoint : checkpoint.(SchedState).(readyList) =
    pending.(os_sched_call_stack).(stackLeaseSlot) :: remove_Z_eqb tid tail).
  { change ((os_sched_ready_checkpoint waiting).(readyList) =
      pending.(os_sched_call_stack).(stackLeaseSlot) :: remove_Z_eqb tid tail).
    rewrite (proj1 (os_sched_ready_checkpoint_frame waiting)); exact Hready. }
  assert (Hdestination : forall outgoing sp, os_sched_destination_binding
    environment.(task_stack_call_external) context outgoing
      (os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot) sp)
      pending.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)).
  { intros outgoing sp.
    assert (Hpending_node : exists pending_node, checkpoint.(TskState).(inUsedTaskStates)
      pending.(os_sched_call_stack).(stackLeaseSlot) = Some pending_node /\
      pending_node.(taskGeneration) = pending.(os_sched_call_stack).(stackLeaseGeneration) /\
      pending_node.(tcbStkPtr) = suspended.(armv7a_continuation_sp))
      by (rewrite <- Hlease; exact Hwaiting_pointer).
    destruct Hpending_node as [pending_node [Hpn [Hpg Hpsp]]].
    assert (Hparked_checkpoint : checkpoint.(TskState).(parkedTaskStacks)
      (task_stack_key pending.(os_sched_call_stack)) =
      Some (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)))
      by exact Hparked.
    assert (Hpark : task_stack_park_fragments checkpoint.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) outgoing (task_stack_key pending.(os_sched_call_stack)) =
      Some (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
    { rewrite task_stack_park_fragments_lookup_other; assumption. }
    assert (Hlive : task_stack_live_binding checkpoint.(TskState) pending.(os_sched_call_stack)).
    { assert (Hconsistent : parked_stacks_consistent checkpoint.(TskState) checkpoint.(TskState).(parkedTaskStacks))
        by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hcheckpoint_valid; tauto).
      exists pending_node; split; [exact Hpn|].
      pose proof (proj2 (proj2 (proj2 (Hconsistent _ _ _ _ Hparked_checkpoint))) pending_node Hpn Hpg) as Hmatches.
      destruct pending.(os_sched_call_stack); exact Hmatches. }
    assert (Hpriority : checkpoint.(SchedState).(highRdyPrio) = Some pending_node.(curPrio)).
    { unfold sched_high_ready_consistency in Hhigh; rewrite Hready_checkpoint in Hhigh.
      destruct Hhigh as [_ [high_node [Hhn Hhp]]]; rewrite Hpn in Hhn;
        injection Hhn as Heq; subst high_node; exact Hhp. }
    assert (Hdest : os_sched_destination_binding environment.(task_stack_call_external) context outgoing checkpoint
      pending.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)).
    { match type of Hprefix_owned with ?P prefix_heap => assert (Hobserve : P |-- coq_prop
        (os_sched_destination_binding environment.(task_stack_call_external) context outgoing checkpoint
          pending.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)) && TT) end.
      { unfold os_sched_source_switch_pre, armv7a_task_call_stacks; Intros.
        sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_call_stack_entry abi checkpoint.(TskState) focus)
          checkpoint.(TskState).(parkedTaskStacks) pending.(os_sched_call_stack)
          suspended.(armv7a_continuation_fragments) Hparked_checkpoint).
        pose proof (task_create_pending_entry_destination environment task_abi context outgoing checkpoint pending
          suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) suspended.(armv7a_continuation_fragments)
          pending_node Hselected_tid Hpn Hpg Hpriority Hlive Hpark) as Hfrom_entry.
        fold abi focus in Hfrom_entry; sep_apply_l_atomic Hfrom_entry; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve prefix_heap Hprefix_owned)). }
    assert (Hlookup : (os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot) sp)
      .(TskState).(inUsedTaskStates) pending.(os_sched_call_stack).(stackLeaseSlot) = Some pending_node).
    { unfold os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      assert (Heq : Z.eqb pending.(os_sched_call_stack).(stackLeaseSlot) context.(os_sched_call_stack).(stackLeaseSlot) = false)
        by (apply Z.eqb_neq; rewrite Htid; exact Hdifferent).
      rewrite Heq; exact Hpn. }
    destruct Hdest as [Hh [Hn [Hl Hp]]].
    unfold os_sched_destination_binding; split.
    - unfold os_sched_save_current_sp; rewrite Hnode; exact Hh.
    - split.
      + destruct Hn as [n [Hdest_node [Hg [Hprio Harch]]]]; rewrite Hpn in Hdest_node; injection Hdest_node as Heq; subst n.
        exists pending_node; split; [exact Hlookup|]. split; [exact Hg|]. split; [|exact Harch].
        unfold os_sched_save_current_sp; rewrite Hnode; exact Hprio.
      + split.
        * destruct Hl as [n [Hlive_node Hmatches]]; rewrite Hpn in Hlive_node; injection Hlive_node as Heq; subst n.
          exists pending_node; split; assumption.
        * unfold os_sched_save_current_sp; rewrite Hnode; exact Hp. }
  exists prefix_heap; split; [exact Hprefix|]. split; [exact Hcur|]. split; [exact Hnode|].
  split; [exact Hid|]. split; [exact Hgen|]. split; [exact Hhigh|].
  split; [rewrite Hready_checkpoint; discriminate|]. split; [rewrite Htid; congruence|].
  split; [exact Hwaiting_pointer|]. split; [exact Hhistory|]. split; [exact Hdestination|].
  exact Hprefix_owned.
Qed.

(** The actual wait prefix above is consumed here by the adopted private
    TCB initializer.  The foreign task's newly created Save handles remain
    in the disjoint caller frame.  The original resumes directly at its
    interrupted field/hook boundary, with no additional CPU Restore. *)
Lemma task_tcb_init_foreign_wait_private_source : forall schedule environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg context foreign_mask entry eid event tid old timeout tail original pending suspended
  args initial_name initial_state detached previous slot free_image commands image
  old_sp cpsr values lr save_prefix save_suffix first old_words publication
  handler_region handler_fragments (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  let fragments := save_prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ save_suffix in
  let foreign_saved := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  task_tcb_init_stack_same_call pending original ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached previous ->
  task_tcb_init_stack_source_preserved original initial_state previous ->
  Forall (task_tcb_init_private_command_valid sg) commands ->
  fold_left task_tcb_init_private_command_image commands image =
    task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) (task_tcb_init_stack_call_args args initial_name) free_image ->
  UCOS2_state_inv sg previous ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) previous entry ->
  sem_pend_wait_entry sg entry eid event tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) = tid :: pending.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  pending.(os_sched_call_origin) = RunningInvocation pending.(os_sched_call_stack).(stackLeaseSlot)
    pending.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some pending ->
  armv7a_task_frame_slice suspended ->
  task_invocation_active entry.(TskState) pending.(os_sched_call_invocation) pending.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key pending.(os_sched_call_stack)) =
    Some (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  0 <= timeout < 4294967296 ->
  context.(os_sched_call_fragments) = save_prefix ++ [(first, first + 16, old_words)] ++ save_suffix ->
  valid_task_stack_region context.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range context.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened entry.(TskState) publication context.(os_sched_call_stack).(stackLeaseSlot)
    context.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall key, tcb_field_address (task_slot_addr sg key) TCBStkPtr = task_slot_addr sg key) ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) foreign_mask entry **
   os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
   (task_slot_storage_rep sg slot image ** task_stack_fragments_rep handler_region handler_fragments ** frame)) before ->
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid old timeout before waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = foreign_mask ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask foreign_mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers acquired saved_heap /\
        acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi context foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg pending.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi context selected installed restored ->
                task_tcb_init_private_irq_continuation schedule environment critical sg args initial_name
                  handler_region handler_fragments original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
                  initial_state detached slot free_image (armv7a_continuation_resumed_call selected pending)
                  (os_sched_install_context context fragments pending.(os_sched_call_stack) updated)
                  commands image restored
                  (interrupt_platform_saved environment.(task_stack_call_platform)
                     (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
                   critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame))))).
Proof.
  intros schedule environment critical arch save restore task_abi sg context foreign_mask entry eid event tid old timeout tail
    original pending suspended args initial_name initial_state detached previous slot free_image commands image
    old_sp cpsr values lr save_prefix save_suffix first old_words publication handler_region handler_fragments frame before
    abi focus waiting checkpoint fragments foreign_saved updated Hsame Hprevious Hordinary Hcommands Himage Hvalid_previous
    Hhistory Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice Hactive Hpointer Hparked
    Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Hpre.
  set (buffer := task_slot_storage_rep sg slot image ** task_stack_fragments_rep handler_region handler_fragments ** frame).
  destruct (task_create_foreign_wait_init_checkpoint environment critical arch save restore task_abi sg context
    foreign_mask entry eid event tid old timeout tail pending suspended buffer before Hentry Hsource Hcache Henabled
    Hlist Habsent Hcoverage Hbinding Hcall Hactive Hpointer Hparked Htimeout Hpre) as [waited [Hstores Hprefix]].
  fold abi focus waiting checkpoint in Hprefix.
  exists waited; split; [exact Hstores|].
  intros cursor written middle final_cursor released Hr0 Hcursor_mask Hrestore_prefix Hrestore_suffix.
  destruct (Hprefix cursor written middle final_cursor released Hr0 Hcursor_mask Hrestore_prefix Hrestore_suffix)
    as [Hrestore_execution Hafter_restore].
  split; [exact Hrestore_execution|].
  intros registers final_registers acquired saved_heap Hreturn Hvalid_sr Hsave_mask Hsave.
  destruct (Hafter_restore registers final_registers acquired saved_heap Hreturn Hvalid_sr Hsave_mask Hsave)
    as [Hsave_execution [Hacquired [prefix_heap [Hprefix_execution [Hcur [Hnode [Hid [Hgen [Hhigh
      [Hnonempty [Hdifferent [Hsaved_pointer [Hwait_history [Hdestination Howned]]]]]]]]]]]]]].
  set (node := task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)) in *.
  assert (Hinput : os_sched_source_live_save_input sg checkpoint node context old_sp cpsr values lr
    save_prefix save_suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input; repeat first [assumption | split].
    intro Heq; exfalso; apply Hdifferent; exact (f_equal fst Heq). }
  assert (Hnext_history : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) previous checkpoint).
  { rewrite (proj1 Hsame) in Hwait_history.
    eapply task_tcb_init_call_preserved_trans; eassumption. }
  set (retained := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
    critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame).
  match type of Howned with ?P prefix_heap => assert (Horder : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg context focus checkpoint ** unmap_table_rep sg **
    task_slot_storage_rep sg slot image ** task_stack_fragments_rep handler_region handler_fragments ** retained)
    by (unfold buffer, retained; entailer!) end.
  destruct (task_tcb_init_private_foreign_capture_return_source schedule environment critical arch task_abi save restore
    sg args initial_name original pending initial_state detached previous slot free_image commands image suspended
    checkpoint node context old_sp cpsr values lr save_prefix save_suffix first old_words publication handler_region
    handler_fragments prefix_heap retained Hsame Hprevious Hordinary Hcommands Himage Hvalid_previous Hnext_history
    Horigin Hbinding Hcall Hslice Hdifferent Hsaved_pointer Hinput (Horder prefix_heap Howned))
    as [stack_written [stored [Hwrites [Hload [Hstore Hcapture]]]]].
  fold fragments foreign_saved updated in Hstore, Hcapture.
  split; [exact Hsave_execution|]. split; [exact Hacquired|].
  exists prefix_heap, stack_written, stored; split; [exact Hprefix_execution|].
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  exact (Hcapture captured hooked Hcaptured Hhook_heap Hhook_step (Hdestination _ _)).
Qed.

(** End-to-end initial-activation consumer for the private-TCB interval.
    The shared selected owner, the actual next SemPend entry and first Save
    feed the proved wait/selector/capture/initializer chain. The linked
    application boundary and port/hook transitions stay explicit. *)
Lemma task_tcb_init_selected_wait_private_source : forall schedule environment critical arch
  (initial : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg incoming selected node state eid event timeout tail original pending suspended
  args initial_name initial_state detached prior slot free_image commands image
  old_sp cpsr values lr save_prefix save_suffix first old_words publication
  handler_region handler_fragments (frame : Assertion)
  before entered first_registers first_final acquired after,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let previous := kernel_selected_call selected state in
  let registered := kernel_selected_call_state selected state in
  let call := kernel_sequential_call previous registered.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) registered.(TskState)) registered in
  let waiting := event_pend_state sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) node PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  let fragments := save_prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ save_suffix in
  let foreign_saved := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments) ->
  state.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio) ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  task_tcb_init_stack_same_call pending original ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached prior ->
  task_tcb_init_stack_source_preserved original initial_state prior ->
  Forall (task_tcb_init_private_command_valid sg) commands ->
  fold_left task_tcb_init_private_command_image commands image =
    task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) (task_tcb_init_stack_call_args args initial_name) free_image ->
  UCOS2_state_inv sg prior ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) prior state ->
  state.(SchedState).(readyList) =
    call.(os_sched_call_stack).(stackLeaseSlot) :: pending.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  pending.(os_sched_call_origin) = RunningInvocation pending.(os_sched_call_stack).(stackLeaseSlot)
    pending.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some pending ->
  armv7a_task_frame_slice suspended ->
  task_invocation_active state.(TskState) pending.(os_sched_call_invocation) pending.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key pending.(os_sched_call_stack)) =
    Some (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  mutex_query_lookup state eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  0 <= timeout < 4294967296 ->
  call.(os_sched_call_fragments) = save_prefix ++ [(first, first + 16, old_words)] ++ save_suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall key, tcb_field_address (task_slot_addr sg key) TCBStkPtr = task_slot_addr sg key) ->
  (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg focus incoming selected node state ** unmap_table_rep sg **
   (task_slot_storage_rep sg slot image ** task_stack_fragments_rep handler_region handler_fragments ** frame)) before ->
  kernel_sequential_call_source boundary previous registered.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered ->
  uchar_load sg.(g_OSIntNesting) 0 entered -> uchar_load sg.(g_OSLockNesting) 0 entered ->
  first_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr first_registers) entry entered first_final acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after -> uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  kernel_call_save_uninterrupted_execution arch first_registers entry entered first_final acquired after /\
  acquired = entry /\
  exists waited,
    sem_pend_wait_fragment sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) node timeout after waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = first_final.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask first_final.(kernel_save_r0) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers acquired saved_heap /\
        acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi call foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg pending.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi call selected installed restored ->
                task_tcb_init_private_irq_continuation schedule environment critical sg args initial_name
                  handler_region handler_fragments original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
                  initial_state detached slot free_image (armv7a_continuation_resumed_call selected pending)
                  (os_sched_install_context call fragments pending.(os_sched_call_stack) updated)
                  commands image restored
                  (interrupt_platform_saved environment.(task_stack_call_platform)
                     (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
                   critical_region_inside critical sg call.(os_sched_call_invocation) waiting ** frame))))).
Proof.
  intros schedule environment critical arch initial boundary save restore task_abi sg incoming selected node state eid event
    timeout tail original pending suspended args initial_name initial_state detached prior slot free_image commands image
    old_sp cpsr values lr save_prefix save_suffix first old_words publication handler_region handler_fragments frame
    before entered first_registers first_final acquired after abi focus previous registered call entry waiting checkpoint
    fragments foreign_saved updated Hnone Hinitial Hinitial_geometry Hrunning Hnonidle Hevent Hmulti Hflag
    Hsame Hprevious Hordinary Hcommands Himage Hvalid_prior Hhistory Hlist Habsent Horigin Hbinding Hcall Hslice
    Hactive Hpointer Hparked Hlookup Hnonnull Hlayout Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication
    Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Hpre Hboundary Htype Hint Hlock Hreturn Hfirst_cpsr
    Hfirst_mask Hfirst_save Hlow Hhigh.
  set (buffer := task_slot_storage_rep sg slot image ** task_stack_fragments_rep handler_region handler_fragments ** frame).
  destruct (task_create_selected_initial_wait_entry_source environment critical arch initial boundary save sg incoming
    selected node state pending suspended eid event before entered first_registers first_final acquired after buffer
    Hnone Hinitial Hinitial_geometry Hparked Hrunning Hnonidle Hevent Hmulti Hflag Hactive Hpointer Hlookup Hnonnull
    Hlayout Hpre Hboundary Htype Hint Hlock Hreturn Hfirst_cpsr Hfirst_mask Hfirst_save Hlow Hhigh)
    as [Hsave_execution [Hacquired [Henabled [Hentry_history [Hentry_active [Hentry_pointer [Hcoverage
      [Hwait [Hsource [Hcache Howned]]]]]]]]]].
  fold abi focus call entry in Hsave_execution, Hacquired, Henabled, Hentry_history, Hentry_active,
    Hentry_pointer, Hcoverage, Hwait, Hsource, Hcache, Howned.
  assert (Hhistory_entry : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) prior entry).
  { rewrite (proj1 Hsame) in Hentry_history.
    eapply task_tcb_init_call_preserved_trans; eassumption. }
  assert (Hlist_entry : entry.(SchedState).(readyList) =
    call.(os_sched_call_stack).(stackLeaseSlot) :: pending.(os_sched_call_stack).(stackLeaseSlot) :: tail).
  { unfold entry, registered, kernel_selected_call_state; rewrite Hnone; exact Hlist. }
  assert (Habsent_entry : entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None).
  { unfold entry, registered, kernel_selected_call_state; rewrite Hnone; exact Habsent. }
  assert (Hparked_entry : entry.(TskState).(parkedTaskStacks) (task_stack_key pending.(os_sched_call_stack)) =
    Some (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { unfold entry, registered, kernel_selected_call_state; rewrite Hnone; exact Hparked. }
  assert (Hpublication_entry : task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration)).
  { unfold entry, registered, kernel_selected_call_state; rewrite Hnone; exact Hpublication. }
  split; [exact Hsave_execution|]. split; [exact Hacquired|].
  exact (task_tcb_init_foreign_wait_private_source schedule environment critical arch save restore task_abi sg call
    first_final.(kernel_save_r0) entry eid event call.(os_sched_call_stack).(stackLeaseSlot) node timeout tail
    original pending suspended args initial_name initial_state detached prior slot free_image commands image
    old_sp cpsr values lr save_prefix save_suffix first old_words publication handler_region handler_fragments frame after
    Hsame Hprevious Hordinary Hcommands Himage Hvalid_prior Hhistory_entry Hwait Hsource Hcache Henabled Hlist_entry
    Habsent_entry Hcoverage Horigin Hbinding Hcall Hslice Hentry_active Hentry_pointer Hparked_entry Htimeout
    Hfragments Hregion Hgeometry Hsp_range Hpublication_entry Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Howned).
Qed.

(** The same produced checkpoint is consumed at a partial child-stack
    boundary.  No future destination or post-return owner is an input. *)
Lemma task_create_foreign_wait_stack_init_source : forall schedule environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg context foreign_mask entry eid event tid old timeout tail original pending suspended
  args region lower upper initial_name task_return initial_state previous prefix suffix
  old_sp cpsr values lr save_prefix save_suffix first old_words publication
  handler_region handler_fragments (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  let fragments := save_prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ save_suffix in
  let foreign_saved := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  task_tcb_init_stack_same_call pending original ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial_state ->
  task_create_stack_init_entry_preserved sg args original initial_state previous ->
  task_tcb_init_stack_source_preserved original initial_state previous ->
  prefix ++ suffix = task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return ->
  Forall (fun word => 0 <= word < 4294967296) suffix ->
  UCOS2_state_inv sg previous ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) previous entry ->
  sem_pend_wait_entry sg entry eid event tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) = tid :: pending.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  pending.(os_sched_call_origin) = RunningInvocation pending.(os_sched_call_stack).(stackLeaseSlot)
    pending.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some pending ->
  armv7a_task_frame_slice suspended ->
  task_invocation_active entry.(TskState) pending.(os_sched_call_invocation) pending.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key pending.(os_sched_call_stack)) =
    Some (pending.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  0 <= timeout < 4294967296 ->
  context.(os_sched_call_fragments) = save_prefix ++ [(first, first + 16, old_words)] ++ save_suffix ->
  valid_task_stack_region context.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range context.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened entry.(TskState) publication context.(os_sched_call_stack).(stackLeaseSlot)
    context.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall key, tcb_field_address (task_slot_addr sg key) TCBStkPtr = task_slot_addr sg key) ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) foreign_mask entry **
   os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
   (task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix ** task_stack_fragments_rep handler_region handler_fragments ** frame)) before ->
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid old timeout before waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = foreign_mask ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask foreign_mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers acquired saved_heap /\
        acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi context foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg pending.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi context selected installed restored ->
                task_create_stack_init_irq_continuation schedule environment critical sg args region handler_region
                  handler_fragments task_return lower upper initial_name original
                  (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) initial_state
                  (armv7a_continuation_resumed_call selected pending)
                  (os_sched_install_context context fragments pending.(os_sched_call_stack) updated)
                  prefix suffix restored
                  (interrupt_platform_saved environment.(task_stack_call_platform)
                     (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
                   critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame))))).
Proof.
  intros schedule environment critical arch save restore task_abi sg context foreign_mask entry eid event tid old timeout tail
    original pending suspended args region lower upper initial_name task_return initial_state previous prefix suffix
    old_sp cpsr values lr save_prefix save_suffix first old_words publication handler_region handler_fragments frame before
    abi focus waiting checkpoint fragments foreign_saved updated Hsame Hlayout Hinitentry Hentry_before Hordinary Hwords Hword_ranges Hvalid_previous
    Hhistory Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice Hactive Hpointer Hparked
    Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Hpre.
  set (buffer := task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix ** task_stack_fragments_rep handler_region handler_fragments ** frame).
  destruct (task_create_foreign_wait_init_checkpoint environment critical arch save restore task_abi sg context
    foreign_mask entry eid event tid old timeout tail pending suspended buffer before Hentry Hsource Hcache Henabled
    Hlist Habsent Hcoverage Hbinding Hcall Hactive Hpointer Hparked Htimeout Hpre) as [waited [Hstores Hprefix]].
  fold abi focus waiting checkpoint in Hprefix.
  exists waited; split; [exact Hstores|].
  intros cursor written middle final_cursor released Hr0 Hcursor_mask Hrestore_prefix Hrestore_suffix.
  destruct (Hprefix cursor written middle final_cursor released Hr0 Hcursor_mask Hrestore_prefix Hrestore_suffix)
    as [Hrestore_execution Hafter_restore].
  split; [exact Hrestore_execution|].
  intros registers final_registers acquired saved_heap Hreturn Hvalid_sr Hsave_mask Hsave.
  destruct (Hafter_restore registers final_registers acquired saved_heap Hreturn Hvalid_sr Hsave_mask Hsave)
    as [Hsave_execution [Hacquired [prefix_heap [Hprefix_execution [Hcur [Hnode [Hid [Hgen [Hhigh
      [Hnonempty [Hdifferent [Hsaved_pointer [Hwait_history [Hdestination Howned]]]]]]]]]]]]]].
  set (node := task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)) in *.
  assert (Hinput : os_sched_source_live_save_input sg checkpoint node context old_sp cpsr values lr
    save_prefix save_suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input; repeat first [assumption | split].
    intro Heq; exfalso; apply Hdifferent; exact (f_equal fst Heq). }
  assert (Hnext_history : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) previous checkpoint).
  { rewrite (proj1 Hsame) in Hwait_history.
    eapply task_tcb_init_call_preserved_trans; eassumption. }
  set (retained := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
    critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame).
  match type of Howned with ?P prefix_heap => assert (Horder : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg context focus checkpoint ** unmap_table_rep sg **
    task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix ** task_stack_fragments_rep handler_region handler_fragments ** retained)
    by (unfold buffer, retained; entailer!) end.
  destruct (task_create_stack_init_foreign_capture_return_source schedule environment critical arch task_abi save restore
    sg args region lower upper initial_name task_return original pending initial_state previous suspended
    checkpoint node context old_sp cpsr values lr save_prefix save_suffix first old_words publication prefix suffix
    handler_region handler_fragments prefix_heap retained Hsame Hlayout Hinitentry Hentry_before Hordinary
    Hwords Hword_ranges Hvalid_previous Hnext_history
    Horigin Hbinding Hcall Hslice Hdifferent Hsaved_pointer Hinput (Horder prefix_heap Howned))
    as [stack_written [stored [Hwrites [Hload [Hstore Hcapture]]]]].
  fold fragments foreign_saved updated in Hstore, Hcapture.
  split; [exact Hsave_execution|]. split; [exact Hacquired|].
  exists prefix_heap, stack_written, stored; split; [exact Hprefix_execution|].
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  exact (Hcapture captured hooked Hcaptured Hhook_heap Hhook_step (Hdestination _ _)).
Qed.
