Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** All actual non-switch C guards share this consumer. The ready-list
    obligation follows from Del's CURRENT task stage and the current
    invariant, only when selection is enabled. The exact original pool
    and all generic locals survive the local Save/C-prefix/Restore chain.
    No old emp-only return interface is used. *)
Lemma mutex_del_continuation_sched_nonswitch_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical arch)
    saved_local sg original mask state registers before final_registers acquired saved_heap
    (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (mutex_del_continuation_source_sched_pre environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) saved_local sg original mask state ** frame) before ->
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
      (mutex_del_continuation_return environment environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) saved_local sg original mask ** frame) after).
Proof.
  intros environment critical arch save restore saved_local sg original mask state registers before
    final_registers acquired saved_heap frame Hreturn Hregisters Hmask Hnoswitch Hpre Hsave.
  set (abi := environment.(mutex_del_call_continuations)).
  set (other := task_create_continuation_local saved_local).
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_del_task_call_stage original state /\ UCOS2_state_inv sg state /\
      mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_continuation_call_closed abi kernel_program_inv other sg
      (task_stack_call_active_key original) original mask state **
      (event_private_pool_rep sg state.(EventState) ** frame))) end.
  { unfold mutex_del_continuation_source_sched_pre; Intros_p Hstage.
    unfold mutex_del_continuation_entry; Intros environment0.
    destruct H as [Henvironment Heq]; subst environment0.
    unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources,
      kernel_program_inv, abi, other; entailer!. }
  destruct (Hopen before Hpre) as [[Hstage [Hvalid [Hreachable Htypes]]] Howned].
  assert (Hnonempty : os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []).
  { intro Henabled; eapply mutex_del_task_call_stage_ready; eassumption. }
  destruct (os_sched_modular_nonswitch_continuation_call environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) critical arch abi save restore
    other sg (task_stack_call_active_key original) original mask state registers before final_registers acquired
    saved_heap (event_private_pool_rep sg state.(EventState) ** frame) Hreturn Hregisters Hmask Hnoswitch
    Hnonempty Howned Hsave) as [Hacquired [Hsave_run [prefix_heap [Hprefix Htail]]]].
  split; [exact Hacquired|]. split; [exact Hsave_run|]. exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hcurrent_mask Hprefix_run Hsuffix_run.
  destruct (Htail cursor written middle final_cursor after Hr0 Hcurrent_mask Hprefix_run Hsuffix_run)
    as [Hrestore_run Hclosed].
  assert (Hreachable_now : mutex_program_selected_reachable sg (os_sched_prefix_state state)).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|]. apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hevents : (os_sched_prefix_state state).(EventState) = state.(EventState)) by reflexivity.
  split; [exact Hrestore_run|].
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold mutex_del_continuation_return, mutex_del_continuation_return_at.
    Exists original (os_sched_prefix_state state) environment.
    unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources,
      mutex_del_callsite_environment, kernel_stack_call_same_call, abi, other in *.
    rewrite Hevents; entailer!. }
  exact (Hclose after Hclosed).
Qed.

(** Actual same-task switch family, including the stale-current-priority
    case already admitted by the Scheduler model. The public Del caller
    owner supplies reachability, all private ECB bytes/types and every
    saved local. The existing Save, C prefix, capture, empty reference
    hook, selection/install, TaskRestore and C Restore meet on identical
    heaps. No final world, final type exclusion or destination binding is
    an input. The current high-cache observation identifies this branch;
    it does not prohibit foreign-task branches of the public API.

    The explicit geometry and absent-active-key facts are the existing
    actual save-cut inputs. They are not additional future-safety or
    eventual-return promises. Nonempty hooks and intervening foreign C
    execution require their actual resource producers. *)
Lemma mutex_del_continuation_sched_self_switch_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical arch)
    (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations))
    (initial : Armv7aInitialEntryABI environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
      environment.(mutex_del_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical arch)
    saved_local sg original mask state registers final_registers acquired saved_heap before
    node old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image original old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = true ->
  checkpoint.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = original.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  original.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region original.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range original.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    original.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range original.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = original.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (mutex_del_continuation_source_sched_pre environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) saved_local sg original mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi original descriptor stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg updated updated ->
      exists installed selected,
        os_sched_switch_source environment.(mutex_del_call_external) sg state original
          (os_sched_install_context original fragments original.(os_sched_call_stack) updated) /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
        (forall restored,
          armv7a_task_restore_transition task_abi original selected installed restored ->
          let current := os_sched_install_context original fragments original.(os_sched_call_stack) updated in
          let returned := kernel_selected_call selected current in
          kernel_stack_call_same_call returned original /\ kernel_call_task_source returned current /\
          (forall cursor written_cursor middle final_cursor after,
            cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
            armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
            armv7a_restore_prefix_transition restore cursor restored written_cursor middle ->
            armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
            kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
            (mutex_del_continuation_return environment environment.(mutex_del_call_external)
              environment.(mutex_del_call_platform) saved_local sg original mask ** frame) after))).
Proof.
  intros environment critical arch save task_abi initial restore saved_local sg original mask state registers
    final_registers acquired saved_heap before node old_sp cpsr values lr prefix suffix first old_words publication
    frame checkpoint fragments descriptor updated Hsave_return Hsave_valid Hmask Hswitch Hhead
    Hnode Hid Hgen Habsent Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges
    Hmasked_cpsr Hsp32 Hsp Haddress Hpre Hsave.
  set (abi := environment.(mutex_del_call_continuations)).
  set (other := task_create_continuation_local saved_local).
  assert (Hstage : mutex_del_task_call_stage original state).
  { match type of Hpre with ?P before => assert (Hobserve : P |--
      coq_prop (mutex_del_task_call_stage original state) && TT) end.
    { unfold mutex_del_continuation_source_sched_pre; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  pose proof (proj1 Hstage) as Hsource.
  assert (Hactive_key : task_stack_call_active_key original = Some (task_stack_key original.(os_sched_call_stack))).
  { unfold task_stack_call_active_key; rewrite (proj1 Hsource); reflexivity. }
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (UCOS2_state_inv sg state /\ mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_continuation_call_closed abi kernel_program_inv other sg
      (Some (task_stack_key original.(os_sched_call_stack))) original mask state **
      (event_private_pool_rep sg state.(EventState) ** frame))) end.
  { unfold mutex_del_continuation_source_sched_pre; Intros_p Hstage0.
    unfold mutex_del_continuation_entry; Intros environment0.
    destruct H as [Henvironment Heq]; subst environment0.
    unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources,
      kernel_program_inv, abi, other.
    rewrite Hactive_key; entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid [Hreachable Htypes]] Howned].
  assert (Hnonempty : state.(SchedState).(readyList) <> []).
  { eapply mutex_del_task_call_stage_ready; [exact Hvalid|exact Hstage|].
    exact (proj1 (proj1 (os_sched_requests_switch_iff state) Hswitch)). }
  destruct (kernel_continuation_call_uninterrupted_save environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) critical arch abi save
    kernel_program_inv other sg (Some (task_stack_key original.(os_sched_call_stack))) original state mask
    registers before final_registers acquired saved_heap (event_private_pool_rep sg state.(EventState) ** frame)
    Hsave_return Hsave_valid Hmask Howned Hsave) as [Hacquired [Hr0 [Hsave_run Hmasked]]].
  split; [exact Hacquired|]. split; [exact Hsave_run|]. subst acquired.
  destruct (os_sched_modular_switch_continuation_selection environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) critical abi task_abi initial sg state node
    original final_registers.(kernel_save_r0) state other old_sp cpsr values lr prefix suffix first old_words
    publication saved_heap (event_private_pool_rep sg state.(EventState) ** frame)
    Hswitch Hnonempty Hsource Hnode Hid Hgen Habsent Hfragments Hregion Hgeometry Hsp_range Hpublication
    Hlength Hcpsr Hlr Hranges Hmasked_cpsr Hsp32 Hsp Haddress Hmasked)
    as [prefix_heap [written [stored [Hprefix [Hwrites [Hload [Hstore Hselection]]]]]]].
  fold checkpoint fragments descriptor updated in Hstore, Hselection.
  exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselection captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [resumed [selected_node [Hsave_source [Hsaved [Hdestination [Hselected
      [Hgeneration [Hin [Hready [Hcovered [Hselected_owned Hdispatch]]]]]]]]]]]].
  assert (Hslot : incoming.(stackLeaseSlot) = original.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 Hdestination) as Hhigh.
    change (checkpoint.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot)) in Hhigh; congruence. }
  assert (Hupdated_node : updated.(TskState).(inUsedTaskStates)
    original.(os_sched_call_stack).(stackLeaseSlot) = Some (task_set_saved_sp node descriptor.(armv7a_continuation_sp))).
  { apply os_sched_save_current_sp_live_value; exact Hnode. }
  assert (Hselected_node : selected_node = task_set_saved_sp node descriptor.(armv7a_continuation_sp)).
  { rewrite Hslot in Hselected; congruence. }
  assert (Hkey : task_stack_key incoming = task_stack_key original.(os_sched_call_stack)).
  { unfold task_stack_key; rewrite Hslot; f_equal.
    rewrite Hselected_node in Hgeneration; change (node.(taskGeneration) = incoming.(stackLeaseGeneration)) in Hgeneration.
    congruence. }
  assert (Hlease : incoming = original.(os_sched_call_stack)).
  { pose proof (proj2 (proj2 (proj2 Hdestination))) as Hlookup.
    rewrite Hkey, task_stack_park_fragments_lookup in Hlookup.
    injection Hlookup as Hregion_eq Hresumed.
    destruct incoming as [incoming_region incoming_slot incoming_generation].
    destruct original.(os_sched_call_stack) as [original_region original_slot original_generation].
    change ((incoming_slot, incoming_generation) = (original_slot, original_generation)) in Hkey.
    change (original_region = incoming_region) in Hregion_eq.
    congruence. }
  rewrite Hlease in Hdestination.
  assert (Hactive : task_invocation_active updated.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin)).
  { unfold updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState); rewrite Hnode.
    cbn [replace_TskS TskState].
    apply task_set_saved_sp_preserves_invocation_active with (node := node); [exact Hnode|exact (proj1 (proj2 Hsource))]. }
  assert (Hreachable_updated : mutex_program_selected_reachable sg updated).
  { eapply mutex_program_source_history_reachable with (before := checkpoint).
    - eapply mutex_program_source_step_reachable; [exact Hreachable|]. apply MutexOwnerSourceFrame; reflexivity.
    - apply (mutex_program_saved_sp_source original.(os_sched_call_invocation)
        original.(os_sched_call_stack).(stackLeaseSlot) descriptor.(armv7a_continuation_sp) sg checkpoint); reflexivity. }
  set (local := kernel_sched_saved_local_at environment.(mutex_del_call_platform) critical sg checkpoint.(TskState)
    original final_registers.(kernel_save_r0) state other).
  fold local in Hselected_owned.
  assert (Hevents : updated.(EventState) = state.(EventState)) by reflexivity.
  match type of Hselected_owned with ?P hooked => assert (Hreturn_input : P |--
    kernel_continuation_inv abi mutex_del_stack_resources local sg
      (Some (task_stack_key original.(os_sched_call_stack))) updated **
    task_stack_fragments_rep original.(os_sched_call_stack).(stackLeaseRegion) fragments **
    kernel_saved_continuation_entry abi updated.(TskState) local
      (task_stack_key original.(os_sched_call_stack)) (original.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    (armv7a_task_switch_control task_abi original ** frame)) end.
  { unfold kernel_continuation_inv, mutex_del_stack_resources; rewrite kernel_program_inv_split_unmap.
    rewrite Hevents; entailer!. }
  destruct (mutex_del_creator_continuation_selected_return environment critical arch task_abi restore sg original
    fragments updated checkpoint.(TskState) original final_registers.(kernel_save_r0) state other resumed hooked frame
    Hactive Hsaved Hdestination Haddress (Hreturn_input hooked Hselected_owned))
    as [installed [selected [Hinstall [Hreads [Hselected_lease Hrestore]]]]].
  exists installed, selected; split.
  - split; [exact Hswitch|].
    exists descriptor.(armv7a_continuation_sp), fragments, updated, original.(os_sched_call_stack), resumed.
    exact (conj Hsave_source (conj Hhook_step (conj Hdestination eq_refl))).
  - split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hselected_lease|].
    intros restored Htask_restore current returned.
    destruct (Hrestore restored Htask_restore) as [Hsame [Hreturned_source Htail]].
    fold current returned in Hsame, Hreturned_source, Htail.
    split; [exact Hsame|]. split; [exact Hreturned_source|].
    intros cursor written_cursor middle final_cursor after Hrestore_r0 Hrestore_mask Hprefix_run Hsuffix_run.
    destruct (Htail cursor written_cursor middle final_cursor after Hrestore_r0 Hrestore_mask Hprefix_run Hsuffix_run)
      as [Hrestore_run Hclosed].
    split; [exact Hrestore_run|]. rewrite Hr0, Hmask in Hclosed.
    match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold mutex_del_continuation_return, mutex_del_continuation_return_at.
      Exists returned current environment.
      unfold mutex_del_callsite_environment; rewrite Hactive_key; unfold abi, other in *; entailer!. }
    exact (Hclose after Hclosed).
Qed.
