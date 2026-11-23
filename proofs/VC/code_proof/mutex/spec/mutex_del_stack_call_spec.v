Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_call_stack_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_pool_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Del's selected source world. The two pure facts describe the actual
    boot/source history and exposed non-Mutex private images. The bytes remain
    the existing program owner and private-map owner, not new ghost fields.
    Type exclusion comes from actual allocator/initializer/Type-last
    source laws, not from mere initializedness or ordinary validity.

    This owner is not equivalent to the former arbitrary-state/weak-map
    entry. No public callee Ensure is installed by defining this instance.
    [active] remains a separate source-cut parameter; None admits Boot. *)
Definition mutex_del_stack_resources sg state : Assertion :=
  coq_prop (mutex_program_selected_reachable sg state /\
    mutex_del_private_types_non_mutex state.(EventState)) &&
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState)).

(** Reuse the existing environment package for hidden ABI/port parameters.
    No new kernel-state or resource Record is needed. The same environment
    must remain in scope through each source producer and returning call. *)
Definition mutex_del_stack_entry_closed external platform sg active call mask state : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform) &&
    kernel_stack_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources sg active call mask state.

Definition mutex_del_stack_registry {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg focus payload cut state : Assertion :=
  coq_prop (mutex_program_selected_reachable sg state /\
    mutex_del_private_types_non_mutex state.(EventState)) &&
  (kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
    sg focus payload cut state ** event_private_pool_rep sg state.(EventState)).

Lemma mutex_del_stack_world_open : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg active state,
  kernel_stack_inv abi mutex_del_stack_resources sg active state --||--
  coq_prop (mutex_program_selected_reachable sg state /\
    mutex_del_private_types_non_mutex state.(EventState)) &&
  kernel_stack_inv abi (fun sg state => kernel_program_inv sg state **
    event_private_pool_rep sg state.(EventState)) sg active state.
Proof. intros; unfold kernel_stack_inv, mutex_del_stack_resources; split; entailer!. Qed.

(** Actual IRQ entry for a live source call. Running/current are branch
    observations needed by the real TCB-SP store, not Del API premises.
    No ready/nonwaiting hypothesis is introduced. The actual stack ABI
    and C nesting/SP writes preserve owner-use history and all ECB bytes. *)
Lemma mutex_del_stack_irq_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc)
    saved.(armv7a_continuation_lr) in
  let payload := (call.(os_sched_call_stack).(stackLeaseRegion),
    saved.(armv7a_continuation_fragments)) in
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice saved ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  (os_int_exit_frame_save_pre external platform handler **
    (kernel_stack_inv abi mutex_del_stack_resources sg
      (Some (task_stack_key call.(os_sched_call_stack))) entry ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists entry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap entry_heap /\
    (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed parked **
      (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) entry_heap.
Proof.
  intros external platform port abi sg entry node handler saved publication frame before saved_heap
    call focus payload parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgeneration Habsent
    Haddress Hregion Hgeometry Hpublication Hsp Hpre Hsave.
  match type of Hpre with ?P before =>
    assert (Hopen : P |-- coq_prop (mutex_program_selected_reachable sg entry /\
      mutex_del_private_types_non_mutex entry.(EventState) /\
      task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
      (os_int_exit_frame_save_pre external platform handler **
       (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi entry.(TskState)
         entry.(TskState).(parkedTaskStacks) **
         (unmap_table_rep sg ** event_private_pool_rep sg entry.(EventState) ** frame))))
  end.
  { unfold kernel_stack_inv, mutex_del_stack_resources; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [[Hhistory [Htypes Hcoverage]] Howned].
  destruct (armv7a_irq_source_save_parks_call external platform port abi sg entry node handler saved
    publication (unmap_table_rep sg ** event_private_pool_rep sg entry.(EventState) ** frame)
    before saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgeneration Habsent Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Howned Hsave)
    as [entry_heap [Hwrites [Hentry [Hcovered Hparked]]]].
  assert (Hevent : parked.(EventState) = entry.(EventState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Hreachable : mutex_program_selected_reachable sg parked).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_program_task_fields_source with
      (tid := call.(os_sched_call_stack).(stackLeaseSlot))
      (old := node) (new := task_set_saved_sp node saved.(armv7a_continuation_sp));
      [exact Hnode|reflexivity|reflexivity| |rewrite Hevent; reflexivity].
    unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hlookup : parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { unfold parked, focus, payload, armv7a_irq_live_parked_state; apply task_stack_park_fragments_lookup. }
  exists entry_heap; split; [exact Hwrites|]. split; [exact Hentry|].
  match type of Hparked with ?P entry_heap => match goal with |- ?Q entry_heap =>
    assert (Hclose : P |-- Q) end end.
  { unfold mutex_del_stack_registry; cbn [kernel_client_call_stack_resources].
    unfold kernel_client_call_stack_world, kernel_client_call_stack_facts.
    rewrite kernel_program_inv_split_unmap.
    rewrite Hevent; entailer!. }
  exact (Hclose entry_heap Hparked).
Qed.

(** Consume the existing real registry/pool producer. Source history,
    initialized images and strong focused ownership return at ONE state.
    The named projection remains explicitly included in the actual region;
    other enabled clients still require their independent source adapters. *)
Lemma mutex_del_stack_creator_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients actor creator
  sg observer focus payload cut before next after (frame : Assertion),
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (mutex_del_stack_registry abi sg focus payload cut state ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer None
      origin state false returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (mutex_del_stack_registry abi sg focus payload next returned ** frame) after.
Proof.
  intros external platform port abi clients actor creator sg observer focus payload cut before next after
    frame Hinclude Hforeign Hargs Htrace.
  induction Htrace; intros state origin Hcut Hpre.
  - exists state, origin; split; [constructor|]. split; [constructor|].
    split; assumption.
  -
  assert (Hopen : mutex_del_stack_registry abi sg focus payload cut state ** frame |--
    coq_prop (mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
      sg focus payload cut state ** event_private_pool_rep sg state.(EventState) ** frame)).
  { unfold mutex_del_stack_registry; entailer!. }
  destruct (Hopen before Hpre) as [[Hhistory Htypes] Howned].
  pose proof (proj1 (mutex_del_creator_pool_resources_valid external platform port abi sg focus payload cut state
    frame before Howned)) as Hvalid.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { pose proof Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  destruct (event_private_pool_call_stack_step external platform port Z abi
    (mutex_del_creator_pool_cursor abi focus payload) focus payload
    (mutex_del_creator_interrupt_step creator) (mutex_del_creator_interrupt_effect creator)
    (mutex_del_creator_pool_extension external platform port abi focus payload creator Hargs)
    sg cut before middle_cut middle state frame H Howned) as [middle_state [Hstep Hmiddle]].
  assert (Hreachable : mutex_program_selected_reachable sg middle_state).
  { eapply mutex_program_source_step_reachable; [exact Hhistory|].
    eapply mutex_del_creator_interrupt_state_source; exact Hstep. }
  pose proof (mutex_del_creator_step_preserves_private_non_mutex creator sg cut state middle_cut
    middle_state Hvalid Htypes Hstep) as Hnonmutex_middle.
  assert (Hclose : kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
      sg focus payload middle_cut middle_state ** event_private_pool_rep sg middle_state.(EventState) ** frame |--
    mutex_del_stack_registry abi sg focus payload middle_cut middle_state ** frame).
  { unfold mutex_del_stack_registry; entailer!. }
  destruct (kernel_client_heap_state_step_source external port Z
    (mutex_del_creator_source_client actor creator) sg observer None (mutex_del_creator_interrupt_effect creator)
    ltac:(constructor; constructor) ltac:(intros; constructor; constructor)
    ltac:(intros; constructor; constructor)
    (mutex_del_creator_interrupt_extension_source external port actor creator sg observer Hforeign Hnames)
    cut state middle_cut middle_state origin Hcut Hstep)
    as [Hcompatible [stopped [middle_origin Hsource]]].
  pose proof (mutex_del_creator_source_trace_nonstopping external port actor creator sg observer None
    origin state stopped middle_origin middle_state Hsource) as ->.
  destruct (IHHtrace middle_state middle_origin Hcompatible (Hclose middle Hmiddle))
    as [returned [returned_origin [Hstates [Htail_source [Hnext Hpost]]]]].
  exists returned, returned_origin; split; [econstructor; eassumption|]. split.
  + replace false with (orb false false) by reflexivity.
    eapply kernel_resumption_task_source_trace_trans; [|exact Htail_source].
    eapply kernel_resumption_task_source_trace_inclusion; eassumption.
  + split; assumption.
Qed.

(** The actual selected-frame take and last CPU exchange produce the
    closed strong owner consumed by the generic Save/Restore suffix.
    Only this final Task-map removal frames Event; a preceding arbitrary
    handler interval never receives such a frame rule. *)
Lemma mutex_del_stack_selected_call_return : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus fragments state
  handler (frame : Assertion) heap,
  let incoming := focus.(armv7a_focus_call).(os_sched_call_stack) in
  task_current_at state incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (mutex_del_stack_registry abi sg focus (incoming.(stackLeaseRegion), fragments)
    KernelClientHeapClosed state **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  let restored := os_int_exit_wrapper_restored_state state incoming in
  exists saved,
    armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus saved /\
    (forall final, armv7a_restore_transition abi handler saved heap final ->
      final.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
      (kernel_stack_call_closed abi mutex_del_stack_resources sg (Some (task_stack_key incoming))
        (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
        (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) restored **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) final).
Proof.
  intros external platform port abi sg focus fragments state handler frame heap incoming Hcurrent Haddress Hpre restored.
  match type of Hpre with ?P heap => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_client_call_stack_world abi sg focus (incoming.(stackLeaseRegion), fragments) state **
     (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (event_private_pool_rep sg state.(EventState) ** frame)))) end.
  { unfold mutex_del_stack_registry; cbn [kernel_client_call_stack_resources]; entailer!. }
  destruct (Hopen heap Hpre) as [[Hhistory Htypes] Howned].
  destruct (mutex_del_private_pool_selected_call_return external platform port abi sg focus fragments state
    handler frame heap Hcurrent Haddress (mutex_del_private_types_defined state.(EventState) Htypes) Howned)
    as [saved [Hloads [Hfocus Hreturn]]].
  assert (Hreachable : mutex_program_selected_reachable sg restored).
  { eapply mutex_program_source_step_reachable; [exact Hhistory|].
    apply MutexOwnerSourceFrame; reflexivity. }
  exists saved; split; [exact Hloads|]. split; [exact Hfocus|].
  intros final Hrestore; destruct (Hreturn final Hrestore) as [Hmemory [Htypes_restored Hpost]].
  assert (Hnonmutex_restored : mutex_del_private_types_non_mutex restored.(EventState)) by exact Htypes.
  split; [exact Hmemory|].
  match type of Hpost with ?P final => match goal with |- ?Q final => assert (Hclose : P |-- Q) end end.
  { unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources; entailer!. }
  exact (Hclose final Hpost).
Qed.
