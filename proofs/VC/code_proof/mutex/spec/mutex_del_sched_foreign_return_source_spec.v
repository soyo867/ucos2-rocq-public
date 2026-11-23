Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_foreign_entry_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_switch_return_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_sched_switch_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Del's own OSCtxSw has already stored the original SP and installed
    this selected destination. An initial destination registers its real
    invocation, and a later IRQ saves that foreign task on the same heap.
    The registered creator trace may change the Event pool before actual
    selection returns to Del. The original SP, active call and focused map
    are derived and transported here, not supplied again at the return.

    This is the initial-destination/one-IRQ returning source family. The
    existing architecture, initial-entry and no-write hook contracts remain
    explicit; the theorem neither assumes eventual return nor closes saved
    foreign destinations or all possible interrupt nesting. *)
Lemma mutex_del_sched_initial_irq_return_post : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (initial_entry : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  actor creator sg checkpoint original_node original suspended incoming first_selected first_node
  handler foreign_saved publication saved acquired initial pe eid observed deleted perr old_error
  before saved_heap (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let first_state := os_sched_install_context original suspended.(armv7a_continuation_fragments)
    incoming updated in
  let foreign := armv7a_initial_call first_selected first_state.(TskState).(taskLifecycle).(taskNextInvocation)
    first_selected.(armv7a_continuation_fragments) in
  let entry := armv7a_initial_call_registered first_selected first_state in
  let parked := armv7a_irq_live_parked_state entry foreign foreign_saved.(armv7a_continuation_sp)
    foreign_saved.(armv7a_continuation_fragments) in
  mutex_del_parent_prefix_ok pe initial eid ->
  mutex_owner_source_history sg initial observed ->
  mutex_del_parent_critical_observation sg eid 1 0 0 1 observed deleted ->
  (forall action, mutex_del_creator_source_client actor creator action ->
    critical.(critical_region_clients) action) ->
  actor <> Some original.(os_sched_call_invocation) -> mutex_del_creator_arguments creator ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  checkpoint.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some original_node ->
  original_node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active first_state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  mutex_program_selected_reachable sg first_state ->
  mutex_del_private_types_non_mutex first_state.(EventState) ->
  first_state.(SchedState).(isRunning) = true -> first_state.(IntrState).(intNesting) = 0 ->
  armv7a_initial_frame_binding first_selected -> first_selected.(armv7a_continuation_call) = None ->
  task_stack_fragments_in_range first_selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 first_selected.(armv7a_continuation_fragments) ->
  handler.(os_int_exit_interrupted_call) = foreign ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask first_selected.(armv7a_continuation_cpsr) ->
  armv7a_task_frame_slice foreign_saved -> valid_task_stack_region foreign.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range foreign.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    foreign_saved.(armv7a_continuation_fragments) ->
  task_publication_happened first_state.(TskState) publication
    foreign.(os_sched_call_stack).(stackLeaseSlot) foreign.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range foreign.(os_sched_call_stack).(stackLeaseRegion)
    foreign_saved.(armv7a_continuation_sp) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (os_sched_source_selected_post environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi
     sg focus incoming first_selected first_node first_state ** unmap_table_rep sg **
   event_private_pool_rep sg first_state.(EventState) **
   (interrupt_platform_saved environment.(mutex_del_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (perr # UChar |-> old_error) ** frame)) before ->
  armv7a_save_transition abi handler foreign_saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes foreign_saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      foreign.(os_sched_call_stack).(stackLeaseSlot) foreign_saved.(armv7a_continuation_sp))
      saved_heap registry_heap /\
    (forall closed_heap,
      kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
        KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned returned_origin,
        kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
          KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(mutex_del_call_external)
          environment.(mutex_del_call_port) critical.(critical_region_clients) sg
          original.(os_sched_call_invocation) None original.(os_sched_call_origin)
          parked false returned_origin returned /\
        (returned.(SchedState).(isRunning) = true ->
         os_int_exit_requests_switch true returned = true -> returned.(SchedState).(readyList) <> [] ->
         (os_int_exit_ready_checkpoint true returned).(SchedState).(highRdyTid) =
           Some original.(os_sched_call_stack).(stackLeaseSlot) ->
         kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg
           (os_int_exit_ready_checkpoint true returned) (os_int_exit_ready_checkpoint true returned) ->
         exists prepared installed selected,
           os_int_exit_source_switch_prefix_execution sg closed_heap prepared /\
           sched_install_heap_fragment sg prepared installed
             (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
           (forall irq_return cursor written middle final_cursor after finished,
             armv7a_restore_transition abi handler selected installed irq_return ->
             cursor.(kernel_restore_r0) = saved ->
             cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
             armv7a_restore_prefix_transition restore cursor irq_return written middle ->
             armv7a_restore_suffix_transition restore written middle final_cursor after ->
             kernel_heap_execution [(perr, 0)] after finished ->
             kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
             (mutex_del_runtime_post environment environment.(mutex_del_call_external)
                environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved)
                initial pe 1 eid 0 0 ** (perr # UChar |-> 0) **
              (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                 handler.(os_int_exit_handler_fragments) ** frame)) finished))).
Proof.
  intros environment critical arch restore initial_entry actor creator sg checkpoint original_node original
    suspended incoming first_selected first_node handler foreign_saved publication saved acquired initial pe eid
    observed deleted perr old_error before saved_heap frame abi focus payload updated first_state foreign entry
    parked Hprefix Hhistory Hobservation Hinclude Hactor Harguments Horigin Horiginal_node Horiginal_gen
    Hbinding Hcall Hslice Hmask Hactive Hreachable Htypes Hrunning Hnest Hinitial Hnone Hfragments
    Hhandler Hhandler_mask Hforeign_slice Hregion Hgeometry Hpublication Hsp Haddress Hpre Hsave.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  match type of Hpre with ?P before => assert (Hexpose : P |--
    coq_prop (first_selected.(armv7a_continuation_stack) = incoming /\
      (task_stack_key incoming = armv7a_call_focus_key focus ->
        armv7a_continuation_focus_binding focus first_selected) /\
      sched_current_ready_at first_state.(TskState) first_state.(SchedState) incoming.(stackLeaseSlot) first_node /\
      first_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\ UCOS2_state_inv sg first_state) && TT) end.
  { unfold os_sched_source_selected_post, UCOS2_inv; entailer!; try tauto; intros ? ?; exact I. }
  destruct (Hexpose before Hpre) as [[Hfirst_lease [Hfocused [Hready [Hfirst_gen Hvalid]]]] _].
  assert (Hdifferent_key : task_stack_key incoming <> armv7a_call_focus_key focus).
  { intros Heq; specialize (Hfocused Heq); destruct Hfocused as [Hfocused _]; congruence. }
  assert (Habsent : first_state.(TskState).(parkedTaskStacks) (task_stack_key incoming) = None).
  { unfold first_state, os_sched_install_context; cbn [replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks parkedTaskStacks]; apply task_stack_take_lookup. }
  assert (Hpending : entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { change (first_state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
    unfold first_state, os_sched_install_context; cbn [replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks parkedTaskStacks].
    rewrite task_stack_take_lookup_other by congruence.
    unfold focus, armv7a_call_focus_key, armv7a_call_focus; cbn [armv7a_focus_call].
    rewrite task_stack_park_fragments_lookup; unfold payload; rewrite Hlease; reflexivity. }
  assert (Hpointer : task_saved_pointer_at entry suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { exists (task_set_saved_sp original_node suspended.(armv7a_continuation_sp)).
    rewrite Hlease; split; [|split; [exact Horiginal_gen|reflexivity]].
    change (updated.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) =
      Some (task_set_saved_sp original_node suspended.(armv7a_continuation_sp))).
    unfold updated, os_sched_save_current_sp; rewrite Horiginal_node.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hregistered_active : task_invocation_active entry.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { apply task_begin_invocation_preserves_invocation_active; [|exact Hactive].
    pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hfirst_id : first_node.(taskID) = incoming.(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hactive_nodes.
    destruct Hactive_nodes as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact (proj1 Hready)].
    apply Hdomain; eauto using (proj1 Hready). }
  pose proof (mutex_del_selected_initial_focused_entry environment initial_entry sg focus payload incoming
    first_selected first_node first_state Hinitial Hnone Hfragments Hreachable Htypes Hnest Hpending) as Hregister.
  cbv zeta in Hregister; fold abi foreign entry in Hregister.
  match type of Hpre with ?P before => assert (Hregistered : P |--
    os_int_exit_frame_save_pre environment.(mutex_del_call_external) environment.(mutex_del_call_platform) handler **
    (mutex_del_focused_world abi sg focus payload (Some (task_stack_key foreign.(os_sched_call_stack))) entry **
     (interrupt_platform_saved environment.(mutex_del_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
      (perr # UChar |-> old_error) ** frame))) end.
  { sepcon_assoc_change; sep_apply_l_atomic Hregister.
    unfold os_int_exit_frame_save_pre; rewrite Hhandler, Hhandler_mask.
    change (task_stack_call_active_key foreign) with (Some (task_stack_key foreign.(os_sched_call_stack))).
    entailer!. }
  assert (Hforeign_lease : foreign.(os_sched_call_stack) = incoming)
    by (unfold foreign, armv7a_initial_call; cbn; exact Hfirst_lease).
  assert (Hforeign_current : entry.(SchedState).(curTaskID) = Some foreign.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite Hforeign_lease; exact (proj1 (proj2 Hready))).
  assert (Hforeign_node : entry.(TskState).(inUsedTaskStates) foreign.(os_sched_call_stack).(stackLeaseSlot) =
    Some first_node) by (rewrite Hforeign_lease; exact (proj1 Hready)).
  assert (Hforeign_absent : entry.(TskState).(parkedTaskStacks) (task_stack_key foreign.(os_sched_call_stack)) = None)
    by (rewrite Hforeign_lease; exact Habsent).
  assert (Hforeign_id : first_node.(taskID) = foreign.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite Hforeign_lease; exact Hfirst_id).
  assert (Hforeign_gen : first_node.(taskGeneration) = foreign.(os_sched_call_stack).(stackLeaseGeneration))
    by (rewrite Hforeign_lease; exact Hfirst_gen).
  assert (Hdifferent : suspended.(armv7a_continuation_stack).(stackLeaseSlot) <>
    foreign.(os_sched_call_stack).(stackLeaseSlot)).
  { intros Heq; destruct Hpointer as [old [Hold [Hg Hsp_old]]].
    rewrite Heq in Hold; assert (old = first_node) by congruence; subst old.
    assert (Hkey : task_stack_key foreign.(os_sched_call_stack) = armv7a_call_focus_key focus).
    { unfold task_stack_key, armv7a_call_focus_key, focus, armv7a_call_focus.
      cbn; rewrite <- Hlease; unfold task_stack_key; congruence. }
    rewrite Hkey in Hforeign_absent; congruence. }
  pose proof (mutex_del_foreign_irq_registry _ _ _ abi sg entry first_node handler foreign_saved publication
    focus payload (interrupt_platform_saved environment.(mutex_del_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
      (perr # UChar |-> old_error) ** frame) before saved_heap) as Hregistry.
  cbv zeta in Hregistry; rewrite Hhandler in Hregistry.
  specialize (Hregistry Hforeign_slice Hrunning Hnest Hforeign_current Hforeign_node Hforeign_id Hforeign_gen
    Hforeign_absent (Haddress _) Hregion Hgeometry Hpublication Hsp (Hregistered before Hpre) Hsave).
  destruct Hregistry as [registry_heap [Hwrites [Hstores Hregistry]]].
  assert (Hrunning_entry : entry.(SchedState).(isRunning) = true) by exact Hrunning.
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) foreign.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp first_node foreign_saved.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) foreign.(os_sched_call_stack)
      foreign_saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning_entry.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hforeign_node; reflexivity. }
  assert (Hparked_active : task_invocation_active parked.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { rewrite Htasks; change (task_invocation_active
      (glob_task_set_usedtask entry.(TskState) foreign.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp first_node foreign_saved.(armv7a_continuation_sp)))
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
    eapply task_set_saved_sp_preserves_invocation_active; eassumption. }
  assert (Hparked_pointer : task_saved_pointer_at parked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [old [Hold [Hg Hsp_old]]]; exists old; split; [|auto].
    rewrite Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    destruct (Z.eqb _ _) eqn:Heq; [apply Z.eqb_eq in Heq; contradiction|exact Hold]. }
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  match type of Hregistry with ?P registry_heap => assert (Hregistry_order : P |--
    mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed parked **
    (interrupt_platform_running environment.(mutex_del_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(mutex_del_call_port) handler **
     (interrupt_platform_saved environment.(mutex_del_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
      ((perr # UChar |-> old_error) ** frame)))) by entailer! end.
  destruct (mutex_del_always_selected_irq_return_post environment critical arch restore actor creator sg parked
    original.(os_sched_call_origin) handler original suspended saved acquired initial pe eid observed deleted
    perr old_error registry_heap closed_heap frame Hprefix Hhistory Hobservation Hinclude Hactor Harguments
    Horigin Hbinding Hcall Hslice Hmask Hparked_active Hparked_pointer Htrace (Hregistry_order registry_heap Hregistry))
    as [returned [returned_origin [Hstates [Hsource Hreturn]]]].
  exists returned, returned_origin; split; [exact Hstates|]. split; [exact Hsource|].
  intros Hr Hs Hn Hh Hhook; exact (Hreturn Hr Hs Hn Hh Hhook (Haddress _)).
Qed.

(** Compose Del's real OS_Sched entry through its local Save, C selector,
    outgoing context stores, initial destination, subsequent foreign IRQ,
    registered creator work, selection of the original call, final Restore
    and success-byte store. The conditional clauses describe actual source
    branches; the initial-frame binding is obtained from the owned selected
    stack by the shared producer, never added to Del's public admission. *)
Lemma mutex_del_always_sched_initial_irq_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (initial_abi : Armv7aInitialEntryABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (initial_entry : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  actor creator sg call mask state registers before final_registers acquired saved_heap
  old_sp cpsr values lr prefix suffix first old_words publication
  initial pe eid observed deleted perr old_error (frame : Assertion),
  mutex_del_parent_prefix_ok pe initial eid ->
  mutex_owner_source_history sg initial observed ->
  mutex_del_parent_critical_observation sg eid 1 0 0 1 observed deleted ->
  (forall action, mutex_del_creator_source_client actor creator action ->
    critical.(critical_region_clients) action) ->
  actor <> Some call.(os_sched_call_invocation) -> mutex_del_creator_arguments creator ->
  state.(SchedState).(isRunning) = true ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  os_sched_requests_switch state = true ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values ->
  armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (mutex_del_source_sched_pre environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg call mask state ** (perr # UChar |-> old_error) ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  let abi := environment.(mutex_del_call_continuations) in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    KernelHeapObservation.pointer_load sg.(g_OSTCBCur)
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (KernelHeapStorage.pointer_store_writes
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call suspended stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected,
        os_sched_destination_binding environment.(mutex_del_call_external) call fragments updated incoming resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        (forall selected_heap,
          armv7a_task_restore_transition task_abi call selected installed selected_heap ->
          os_sched_source_switch_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi sg
            checkpoint call old_sp cpsr values lr suspended incoming selected prefix_heap selected_heap /\
          (selected.(armv7a_continuation_call) = None ->
           task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
             0 selected.(armv7a_continuation_fragments) ->
           let first_state := os_sched_install_context call fragments incoming updated in
           let foreign := armv7a_initial_call selected first_state.(TskState).(taskLifecycle).(taskNextInvocation)
             selected.(armv7a_continuation_fragments) in
           let entry := armv7a_initial_call_registered selected first_state in
           forall handler foreign_saved foreign_publication (rest : Assertion),
             frame = task_stack_fragments_rep handler.(os_int_exit_handler_stack)
               handler.(os_int_exit_handler_fragments) ** rest ->
             handler.(os_int_exit_interrupted_call) = foreign ->
             handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) ->
             armv7a_task_frame_slice foreign_saved ->
             valid_task_stack_region foreign.(os_sched_call_stack).(stackLeaseRegion) ->
             task_stack_fragments_in_range foreign.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
               foreign_saved.(armv7a_continuation_fragments) ->
             task_publication_happened first_state.(TskState) foreign_publication
               foreign.(os_sched_call_stack).(stackLeaseSlot) foreign.(os_sched_call_stack).(stackLeaseGeneration) ->
             task_stack_saved_pointer_in_range foreign.(os_sched_call_stack).(stackLeaseRegion)
               foreign_saved.(armv7a_continuation_sp) ->
             forall foreign_saved_heap,
               armv7a_save_transition abi handler foreign_saved selected_heap foreign_saved_heap ->
               let parked := armv7a_irq_live_parked_state entry foreign foreign_saved.(armv7a_continuation_sp)
                 foreign_saved.(armv7a_continuation_fragments) in
               exists registry_heap,
                 kernel_heap_writes (armv7a_continuation_save_writes foreign_saved)
                   selected_heap.(ConAssertion.s_mem) foreign_saved_heap.(ConAssertion.s_mem) /\
                 kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
                   foreign.(os_sched_call_stack).(stackLeaseSlot) foreign_saved.(armv7a_continuation_sp))
                   foreign_saved_heap registry_heap /\
                 (forall closed_heap,
                   kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
                     KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
                   exists returned returned_origin,
                     kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
                       KernelClientHeapClosed parked KernelClientHeapClosed returned /\
                     kernel_resumption_task_source_trace environment.(mutex_del_call_external)
                       environment.(mutex_del_call_port) critical.(critical_region_clients) sg
                       call.(os_sched_call_invocation) None call.(os_sched_call_origin)
                       parked false returned_origin returned /\
                     (returned.(SchedState).(isRunning) = true ->
                      os_int_exit_requests_switch true returned = true -> returned.(SchedState).(readyList) <> [] ->
                      (os_int_exit_ready_checkpoint true returned).(SchedState).(highRdyTid) =
                        Some call.(os_sched_call_stack).(stackLeaseSlot) ->
                      kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg
                        (os_int_exit_ready_checkpoint true returned) (os_int_exit_ready_checkpoint true returned) ->
                      exists prepared return_installed returning,
                        os_int_exit_source_switch_prefix_execution sg closed_heap prepared /\
                        sched_install_heap_fragment sg prepared return_installed
                          (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) returning.(armv7a_continuation_sp) /\
                        (forall irq_return cursor msr_written middle final_cursor after finished,
                          armv7a_restore_transition abi handler returning return_installed irq_return ->
                          cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
                          cursor.(kernel_restore_current_cpsr) = returning.(armv7a_continuation_cpsr) ->
                          armv7a_restore_prefix_transition restore cursor irq_return msr_written middle ->
                          armv7a_restore_suffix_transition restore msr_written middle final_cursor after ->
                          kernel_heap_execution [(perr, 0)] after finished ->
                          kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
                          (mutex_del_runtime_post environment environment.(mutex_del_call_external)
                             environment.(mutex_del_call_platform) sg call mask initial pe 1 eid 0 0 **
                           (perr # UChar |-> 0) **
                           (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                              handler.(os_int_exit_handler_fragments) ** rest)) finished)))))).
Proof.
  intros environment critical arch save restore task_abi initial_abi initial_entry actor creator sg call mask state
    registers before final_registers acquired saved_heap old_sp cpsr values lr prefix suffix first old_words
    publication initial pe eid observed deleted perr old_error frame Hprefix Hhistory Hobservation Hinclude Hactor
    Harguments Hrunning Habsent Hswitch Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range
    Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave
    abi checkpoint fragments suspended updated.
  assert (Hstage : mutex_del_task_call_stage call state).
  { match type of Hpre with ?P before => assert (Hget : P |-- coq_prop (mutex_del_task_call_stage call state) && TT) end.
    { unfold mutex_del_source_sched_pre; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hget before Hpre)). }
  destruct (proj1 Hstage) as [Horigin [Hactive Hcurrent]].
  pose proof (proj2 (proj2 Hactive)) as Hlive; rewrite Horigin in Hlive.
  destruct Hlive as [original_node [Hnode Hgeneration]].
  assert (Hnode_checkpoint : checkpoint.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some original_node) by exact Hnode.
  assert (Hbinding : armv7a_continuation_binding suspended)
    by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hslice : armv7a_task_frame_slice suspended).
  { exists (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) prefix **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) suffix).
    unfold suspended, armv7a_task_save_image, armv7a_continuation_words; cbn.
    unfold fragments; rewrite Hsp; apply armv7a_task_frame_fragments_split. }
  assert (Hsuspended_mask : armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192).
  { unfold suspended, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hswitch_mask. }
  match type of Hpre with ?P before => assert (Horder : P |--
    mutex_del_source_sched_pre environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state ** ((perr # UChar |-> old_error) ** frame))
    by entailer! end.
  destruct (mutex_del_sched_switch_source_initial_frame environment critical arch save task_abi initial_abi sg
    call mask state registers before final_registers acquired saved_heap old_sp cpsr values lr prefix suffix
    first old_words publication ((perr # UChar |-> old_error) ** frame) Habsent Hswitch Hreturn Hvalid_sr Hmask
    Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress
    (Horder before Hpre) Hsave)
    as (Hsave_run & Hacquired & prefix_heap & written & stored & Hselect & Hwrites & Hload & Hstore & Hcontinue).
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask).
  { rewrite (proj1 (kernel_call_save_uninterrupted_return_values arch registers state before
      final_registers acquired saved_heap Hsave_run)); exact Hmask. }
  split; [exact Hsave_run|]. split; [exact Hacquired|]. exists prefix_heap, written, stored.
  split; [exact Hselect|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hheap Hhook.
  destruct (Hcontinue captured hooked Hcapture Hheap Hhook)
    as (incoming & resumed & installed & selected & current & Hdestination & Hactive_now & Hreachable & Htypes &
      Hselected_fragments & Hinstall & Hreads & Hinitial & Hrestore_selected).
  exists incoming, resumed, installed, selected.
  split; [exact Hdestination|]. split; [exact Hinstall|].
  intros selected_heap Hselected_restore.
  destruct (Hrestore_selected selected_heap Hselected_restore) as [Hexecution [Hsource Hselected]].
  split; [exact Hexecution|].
  intros Hnone Hinitial_fragments first_state foreign entry handler foreign_saved foreign_publication rest
    Hframe Hhandler Hhandler_mask Hforeign_slice Hforeign_region Hforeign_geometry Hforeign_publication
    Hforeign_sp foreign_saved_heap Hforeign_save parked.
  assert (Hrunning_selected : first_state.(SchedState).(isRunning) = true).
  { unfold first_state, os_sched_install_context, updated, os_sched_save_current_sp; rewrite Hnode_checkpoint.
    change ((os_sched_ready_checkpoint state).(isRunning) = true).
    rewrite (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame state)))); exact Hrunning. }
  assert (Hnest_selected : first_state.(IntrState).(intNesting) = 0).
  { pose proof (proj1 (proj1 (os_sched_requests_switch_iff _) Hswitch)) as Henabled.
    pose proof (proj1 (proj1 (os_sched_selection_enabled_iff _) Henabled)) as Hzero.
    unfold first_state, os_sched_install_context, updated, os_sched_save_current_sp; rewrite Hnode_checkpoint.
    exact Hzero. }
  assert (Hpool : first_state.(EventState) = state.(EventState)).
  { unfold first_state, os_sched_install_context, updated, os_sched_save_current_sp; rewrite Hnode_checkpoint.
    reflexivity. }
  match type of Hselected with ?P selected_heap => assert (Hselected_order : P |--
    os_sched_source_selected_post environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      environment.(mutex_del_call_port) abi sg (armv7a_call_focus call suspended.(armv7a_continuation_pc)
        suspended.(armv7a_continuation_lr)) incoming selected current first_state ** unmap_table_rep sg **
    event_private_pool_rep sg first_state.(EventState) **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     (perr # UChar |-> old_error) ** rest)) end.
  { rewrite Hframe, Hpool; entailer!. }
  rewrite <- Hsaved_mask.
  exact (mutex_del_sched_initial_irq_return_post environment critical arch restore initial_entry actor creator sg
    checkpoint original_node call suspended incoming selected current handler foreign_saved foreign_publication
    final_registers.(kernel_save_r0) state initial pe eid observed deleted perr old_error selected_heap
    foreign_saved_heap rest Hprefix Hhistory Hobservation Hinclude Hactor Harguments Horigin Hnode_checkpoint
    Hgeneration Hbinding eq_refl Hslice Hsuspended_mask Hactive_now Hreachable Htypes Hrunning_selected
    Hnest_selected (Hinitial Hnone) Hnone Hinitial_fragments Hhandler Hhandler_mask Hforeign_slice Hforeign_region
    Hforeign_geometry Hforeign_publication Hforeign_sp Haddress (Hselected_order selected_heap Hselected) Hforeign_save).
Qed.
