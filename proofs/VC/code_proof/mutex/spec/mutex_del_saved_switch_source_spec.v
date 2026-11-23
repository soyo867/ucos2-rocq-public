Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_foreign_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consume Del's CURRENT stage-aware Scheduler input and the observed
    foreign-selection branch. The public call protocol supplies the
    registered current task and conditional readiness; it does not claim
    that the cached current priority is fresh. Consequently the foreign
    selector condition is explicit at this cut and the possible self
    selection remains a separate source family.

    Actual Save, selector, context stores, capture and installation keep
    the original descriptor and its local saved-mask/inside owners in ONE
    parked entry. The private Event pool and reachable/type properties
    survive that same execution. This ends in foreign task execution, not
    in a return of the original OS_Sched or OSMutexDel. *)
Lemma mutex_del_sched_saved_foreign_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg call mask state registers before final_registers acquired saved_heap
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  os_sched_requests_switch state = true ->
  checkpoint.(SchedState).(highRdyTid) <> Some call.(os_sched_call_stack).(stackLeaseSlot) ->
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
    environment.(mutex_del_call_platform) sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      suspended.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call suspended stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current_node,
        os_sched_destination_binding environment.(mutex_del_call_external) call fragments updated incoming resumed /\
        task_stack_key incoming <> task_stack_key call.(os_sched_call_stack) /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        sched_current_ready_at (os_sched_install_context call fragments incoming updated).(TskState)
          (os_sched_install_context call fragments incoming updated).(SchedState) incoming.(stackLeaseSlot) current_node /\
        current_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
        task_stack_live_coverage (os_sched_install_context call fragments incoming updated).(TskState)
          (Some (task_stack_key incoming)) /\
        (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
        (forall restored,
          armv7a_task_restore_transition task_abi call selected installed restored ->
          let foreign_state := os_sched_install_context call fragments incoming updated in
          os_sched_source_switch_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi sg
            checkpoint call old_sp cpsr values lr suspended incoming selected prefix_heap restored /\
          task_invocation_active foreign_state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
          mutex_program_selected_reachable sg foreign_state /\
          mutex_del_private_types_non_mutex foreign_state.(EventState) /\
          foreign_state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
            Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments) /\
          armv7a_task_restored_source environment.(mutex_del_call_external) selected /\
          (armv7a_task_restored_execution environment.(mutex_del_call_external)
             environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi selected **
           kernel_program_inv sg foreign_state **
           store_parked_continuations
             (kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) state
               suspended foreign_state.(TskState) focus) foreign_state.(TskState).(parkedTaskStacks) **
           (event_private_pool_rep sg foreign_state.(EventState) ** frame)) restored)).
Proof.
  intros environment critical arch save task_abi initial sg call mask state registers before final_registers
    acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame
    abi focus checkpoint fragments suspended updated Habsent Hswitch Hforeign Hreturn Hvalid_sr Hmask
    Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32
    Hsp Haddress Hpre Hsave.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_del_task_call_stage call state /\ UCOS2_state_inv sg state /\
      mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_stack_call_closed abi kernel_program_inv sg (task_stack_call_active_key call) call mask state **
     (event_private_pool_rep sg state.(EventState) ** frame))) end.
  { unfold mutex_del_source_sched_pre, mutex_del_runtime_entry; Intros selected.
    destruct H0 as [Henv Hsame]; subst selected.
    unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources; fold abi.
    rewrite !kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [[Hstage [Hvalid [Hreachable Htypes]]] Hclosed].
  pose proof (proj1 Hstage) as Hsource.
  pose proof Hsource as [Horigin [Hactive Hcurrent]].
  pose proof (proj2 (proj2 Hactive)) as Hlive.
  rewrite Horigin in Hlive.
  destruct Hlive as [node [Hnode Hgen]].
  pose proof (proj1 (proj1 (os_sched_requests_switch_iff state) Hswitch)) as Henabled.
  pose proof (mutex_del_task_call_stage_ready sg call state Hvalid Hstage Henabled) as Hnonempty.
  assert (Hid : node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hlinks.
    destruct Hlinks as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hnode].
    apply Hdomain; eauto. }
  assert (Hcovered : task_stack_live_coverage state.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hclosed with ?P before => assert (Hobserve : P |-- coq_prop
      (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) && TT) end.
    { unfold kernel_stack_call_closed, kernel_stack_inv, task_stack_call_active_key.
      rewrite Horigin; unfold task_stack_key; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hclosed)). }
  assert (Hready : checkpoint.(SchedState).(readyList) = state.(SchedState).(readyList))
    by exact (proj1 (os_sched_ready_checkpoint_frame state)).
  assert (Hhigh : sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState)).
  { apply os_sched_ready_checkpoint_high_consistency with (sg := sg); [|exact Henabled].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  unfold task_execution_current in Hcurrent; rewrite Horigin in Hcurrent.
  assert (Hinput : os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input, focus.
    assert (Hcur : checkpoint.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
    { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch; exact Hcurrent. }
    rewrite Hready; repeat first [assumption | reflexivity | split | intro]. }
  assert (Howned : (kernel_call_execution_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) call mask ** kernel_program_inv sg state **
    armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
    (event_private_pool_rep sg state.(EventState) ** frame)) before).
  { match type of Hclosed with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
    { unfold kernel_stack_call_closed, kernel_stack_inv; fold abi; Intros.
      sep_apply_l_atomic (armv7a_task_call_stacks_absent _ _ _ abi state.(TskState) focus
        state.(TskState).(parkedTaskStacks) Habsent); entailer!. }
    exact (Horder before Hclosed). }
  destruct (kernel_sched_save_foreign_source _ _ _ abi critical arch save task_abi initial
    sg state call node mask focus old_sp cpsr values lr prefix suffix first old_words publication
    registers final_registers acquired before saved_heap (event_private_pool_rep sg state.(EventState) ** frame)
    Hswitch Hnonempty Hforeign Hinput Hcovered Hsource Hreturn Hvalid_sr Hmask Howned Hsave)
    as [Hrun [Hacquired [prefix_heap [written [stored [Hprefix [Hwrites [Hload [Hstore Hselected]]]]]]]]].
  split; [exact Hrun|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselected captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current_node
      [Harch [Hdestination [Hkey [Hlease [Hselected_fragments [Hinstall [Hreads
        [Hparked [Hready_current [Hgen_current [Hcoverage [Hfocus_lookup [Hinitial Hrestore]]]]]]]]]]]]]]]]]].
  set (foreign_state := os_sched_install_context call fragments incoming updated) in *.
  assert (Hactive_after : task_invocation_active foreign_state.(TskState)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { unfold foreign_state, updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; change (task_invocation_active (glob_task_set_usedtask state.(TskState)
      call.(os_sched_call_stack).(stackLeaseSlot) (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
      call.(os_sched_call_invocation) call.(os_sched_call_origin)).
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive]. }
  assert (Hreach_after : mutex_program_selected_reachable sg foreign_state).
  { eapply mutex_program_source_history_reachable; [exact Hreachable|].
    eapply mutex_program_task_fields_source with (tid := call.(os_sched_call_stack).(stackLeaseSlot))
      (old := node) (new := task_set_saved_sp node suspended.(armv7a_continuation_sp));
      [exact Hnode|reflexivity|reflexivity| |].
    - unfold foreign_state, os_sched_install_context, updated, os_sched_save_current_sp,
        checkpoint, os_sched_prefix_state; cbn [replace_SchedS TskState]; rewrite Hnode; reflexivity.
    - unfold foreign_state, os_sched_install_context, updated, os_sched_save_current_sp,
        checkpoint, os_sched_prefix_state; cbn [replace_SchedS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Hevents : foreign_state.(EventState) = state.(EventState)).
  { unfold foreign_state, os_sched_install_context, updated, os_sched_save_current_sp,
      checkpoint, os_sched_prefix_state; cbn [replace_SchedS EventState TskState]; rewrite Hnode; reflexivity. }
  exists incoming, resumed, installed, selected, current_node.
  split; [exact Hdestination|]. split; [exact Hkey|]. split; [exact Hlease|].
  split; [exact Hselected_fragments|]. split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hready_current|]. split; [exact Hgen_current|]. split; [exact Hcoverage|].
  split; [exact Hinitial|].
  intros restored Hrestored; cbv zeta.
  destruct (Hrestore restored Hrestored) as [Hexecution [Hrestored_source Hafter]].
  split; [exact Hexecution|]. split; [exact Hactive_after|]. split; [exact Hreach_after|].
  split.
  { change (mutex_del_private_types_non_mutex foreign_state.(EventState)).
    rewrite Hevents; exact Htypes. }
  split; [exact Hparked|]. split; [exact Hrestored_source|].
  change ((armv7a_task_restored_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi selected **
    kernel_program_inv sg foreign_state **
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) state
        suspended foreign_state.(TskState) focus) foreign_state.(TskState).(parkedTaskStacks) **
    (event_private_pool_rep sg foreign_state.(EventState) ** frame)) restored).
  rewrite Hevents; exact Hafter.
Qed.

