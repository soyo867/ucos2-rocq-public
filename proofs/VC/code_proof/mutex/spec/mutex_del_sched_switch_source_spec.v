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
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consume Del's actual stage-aware Scheduler entry. The C guards and
    current ready node provide nonempty selection; the source cut supplies
    the absent parked key and concrete stack geometry. These facts are
    not inferred from stack coverage or assumed of every future call.

    This executes the next local Save, selector, context stores, capture
    and destination restore. The current private Event pool and original
    saved-mask/inside owner survive precisely these operations. A selected
    foreign task must transport them through its subsequent actual source
    execution before the already proved returning consumer may use them. *)
Lemma mutex_del_sched_switch_source_initial_frame : forall environment critical arch
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
    environment.(mutex_del_call_platform) sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state **
     (event_private_pool_rep sg state.(EventState) ** frame)) in
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
      exists incoming resumed installed selected current,
        os_sched_destination_binding environment.(mutex_del_call_external) call fragments updated incoming resumed /\
        task_invocation_active (os_sched_install_context call fragments incoming updated).(TskState)
          call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
        mutex_program_selected_reachable sg (os_sched_install_context call fragments incoming updated) /\
        mutex_del_private_types_non_mutex (os_sched_install_context call fragments incoming updated).(EventState) /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi sg
            checkpoint call old_sp cpsr values lr suspended incoming selected prefix_heap restored /\
          armv7a_task_restored_source environment.(mutex_del_call_external) selected /\
          (os_sched_source_selected_post environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg focus incoming selected current
            (os_sched_install_context call fragments incoming updated) ** retained) restored)).
Proof.
  intros environment critical arch save task_abi initial sg call mask state registers before final_registers
    acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame Habsent Hswitch
    Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges
    Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave abi focus checkpoint fragments suspended updated retained.
  set (sched_environment := mutex_del_runtime_sched_environment environment).
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_del_task_call_stage call state /\ UCOS2_state_inv sg state /\
      mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_stack_call_closed abi kernel_program_inv sg (task_stack_call_active_key call) call mask state **
     (event_private_pool_rep sg state.(EventState) ** frame))) end.
  { unfold mutex_del_source_sched_pre, mutex_del_runtime_entry; Intros selected.
    destruct H0 as [Henv Hsame]; subst selected.
    unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources.
    rewrite !kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [[Hstage [Hvalid_state [Hreachable Htypes]]] Hclosed].
  pose proof (proj1 (proj1 (os_sched_requests_switch_iff state) Hswitch)) as Henabled.
  pose proof (mutex_del_task_call_stage_ready sg call state Hvalid_state Hstage Henabled) as Hnonempty.
  destruct (proj1 Hstage) as [Horigin [Hactive Hcurrent]].
  pose proof (proj2 (proj2 Hactive)) as Hlive.
  rewrite Horigin in Hlive, Hcurrent.
  destruct Hlive as [node [Hnode Hgeneration]].
  destruct (task_create_tcb_return_sched_masked_source sched_environment critical arch save sg call
    call mask state registers before final_registers acquired saved_heap
    (event_private_pool_rep sg state.(EventState) ** frame)
    ltac:(unfold task_tcb_init_stack_same_call; auto) Hreturn Hvalid_sr Hmask Hclosed Hsave)
    as [_ [Hrun [Hstate [Hr0 Hmasked]]]].
  split; [exact Hrun|]. split; [exact Hstate|]. subst acquired.
  destruct (task_create_sched_masked_switch_prefix_source sched_environment critical sg call
    final_registers.(kernel_save_r0) state state lr saved_heap
    (event_private_pool_rep sg state.(EventState) ** frame) Horigin Habsent Hnonempty Hswitch Hmasked)
    as [prefix_heap [Hprefix [Hhigh [_ Hprefix_owned]]]].
  assert (Hid : node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid_state)))) as Hactive_nodes.
    destruct Hactive_nodes as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hnode].
    apply Hdomain; eauto. }
  assert (Hcheckpoint_current : checkpoint.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch;
      exact Hcurrent. }
  assert (Hcheckpoint_nonempty : checkpoint.(SchedState).(readyList) <> []).
  { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch;
      exact Hnonempty. }
  assert (Hinput : os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input, focus.
    repeat first [assumption | reflexivity | split | intro]. }
  assert (Hactive_updated : task_invocation_active updated.(TskState)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { unfold updated, os_sched_save_current_sp, checkpoint, os_sched_prefix_state.
    cbn [replace_SchedS TskState]; rewrite Hnode.
    cbn [replace_TskS TskState].
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hnode|reflexivity|exact Hactive]. }
  match type of Hprefix_owned with ?P prefix_heap => assert (Horder : P |--
    os_sched_source_switch_pre environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      environment.(mutex_del_call_port) abi sg call focus checkpoint ** retained)
      by (unfold retained; entailer!) end.
  destruct (os_sched_source_live_switch_destination_resources_initial_frame _ _ _ abi task_abi initial sg checkpoint
    node call old_sp cpsr values lr prefix suffix first old_words focus publication retained prefix_heap
    Hinput (Horder prefix_heap Hprefix_owned))
    as [written [stored [Hwrites [Hload [Hstore Hselected]]]]].
  exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselected captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current [Hsource [Hdestination [Hfragments_selected
      [Hinstall [Hreads [Hpending [Hinitial Hrestore]]]]]]]]]]]].
  assert (Hreach_selected : mutex_program_selected_reachable sg
    (os_sched_install_context call fragments incoming updated)).
  { eapply mutex_program_source_history_reachable; [exact Hreachable|].
    eapply mutex_program_task_fields_source with (tid := call.(os_sched_call_stack).(stackLeaseSlot))
      (old := node) (new := task_set_saved_sp node suspended.(armv7a_continuation_sp));
      [exact Hnode|reflexivity|reflexivity| |].
    - unfold os_sched_install_context, updated, os_sched_save_current_sp, checkpoint, os_sched_prefix_state;
        cbn [replace_SchedS TskState]; rewrite Hnode; reflexivity.
    - unfold os_sched_install_context, updated, os_sched_save_current_sp, checkpoint, os_sched_prefix_state;
        cbn [replace_SchedS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Htypes_selected : mutex_del_private_types_non_mutex
    (os_sched_install_context call fragments incoming updated).(EventState)).
  { unfold os_sched_install_context, updated, os_sched_save_current_sp, checkpoint, os_sched_prefix_state;
      cbn [replace_SchedS EventState TskState]; rewrite Hnode; exact Htypes. }
  exists incoming, resumed, installed, selected, current.
  exact (conj Hdestination (conj Hactive_updated (conj Hreach_selected (conj Htypes_selected
    (conj Hfragments_selected (conj Hinstall (conj Hreads (conj Hinitial Hrestore)))))))).
Qed.

(** Original interface retained for existing callers. *)
Lemma mutex_del_sched_switch_source : forall environment critical arch
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
    environment.(mutex_del_call_platform) sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state **
     (event_private_pool_rep sg state.(EventState) ** frame)) in
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
      exists incoming resumed installed selected current,
        os_sched_destination_binding environment.(mutex_del_call_external) call fragments updated incoming resumed /\
        task_invocation_active (os_sched_install_context call fragments incoming updated).(TskState)
          call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
        mutex_program_selected_reachable sg (os_sched_install_context call fragments incoming updated) /\
        mutex_del_private_types_non_mutex (os_sched_install_context call fragments incoming updated).(EventState) /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi sg
            checkpoint call old_sp cpsr values lr suspended incoming selected prefix_heap restored /\
          armv7a_task_restored_source environment.(mutex_del_call_external) selected /\
          (os_sched_source_selected_post environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg focus incoming selected current
            (os_sched_install_context call fragments incoming updated) ** retained) restored)).
Proof.
  intros environment critical arch save task_abi initial sg call mask state registers before final_registers
    acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame Habsent Hswitch
    Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges
    Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave.
  destruct (mutex_del_sched_switch_source_initial_frame environment critical arch save task_abi initial sg
    call mask state registers before final_registers acquired saved_heap old_sp cpsr values lr prefix suffix
    first old_words publication frame Habsent Hswitch Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry
    Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave)
    as (Hrun & Hstate & prefix_heap & written & stored & Hprefix & Hwrites & Hload & Hstore & Hcontinue).
  split; [exact Hrun|]. split; [exact Hstate|]. exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hheap Hhook.
  destruct (Hcontinue captured hooked Hcapture Hheap Hhook)
    as (incoming & resumed & installed & selected & current & Hdestination & Hactive & Hreachable & Htypes &
      Hfragments_selected & Hinstall & Hreads & Hinitial & Hrestore).
  exists incoming, resumed, installed, selected, current.
  exact (conj Hdestination (conj Hactive (conj Hreachable (conj Htypes
    (conj Hfragments_selected (conj Hinstall (conj Hreads Hrestore))))))).
Qed.

(** Del's actual nonzero wait-group continuation consumes the current
    stage-aware owner returned by its outer Restore. The deletion observation
    proves the schedule request via mutex_del_observation_schedule_request;
    the following call uses this current state, including changed priorities.
    The parked-key and stack geometry remain facts of the actual source cut. *)
Lemma mutex_del_returned_call_sched_switch_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg original call mask state registers before final_registers acquired saved_heap
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion),
  mutex_del_schedule_request original 1 ->
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
  (mutex_del_source_return_at environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg original mask call state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state **
     (event_private_pool_rep sg state.(EventState) ** frame)) in
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
      exists incoming resumed installed selected current,
        os_sched_destination_binding environment.(mutex_del_call_external) call fragments updated incoming resumed /\
        task_invocation_active (os_sched_install_context call fragments incoming updated).(TskState)
          call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
        mutex_program_selected_reachable sg (os_sched_install_context call fragments incoming updated) /\
        mutex_del_private_types_non_mutex (os_sched_install_context call fragments incoming updated).(EventState) /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi sg
            checkpoint call old_sp cpsr values lr suspended incoming selected prefix_heap restored /\
          armv7a_task_restored_source environment.(mutex_del_call_external) selected /\
          (os_sched_source_selected_post environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg focus incoming selected current
            (os_sched_install_context call fragments incoming updated) ** retained) restored)).
Proof.
  intros environment critical arch save task_abi initial sg original call mask state registers before final_registers
    acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame Hrequest Habsent Hswitch
    Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges
    Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave.
  assert (Hsched_pre : (mutex_del_source_sched_pre environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg call mask state ** frame) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Hopen : P |-- Q) end end.
    { sep_apply_l_atomic (mutex_del_source_return_sched_pre environment environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) sg original mask call state Hrequest); entailer!. }
    exact (Hopen before Hpre). }
  exact (mutex_del_sched_switch_source environment critical arch save task_abi initial sg call mask state
    registers before final_registers acquired saved_heap old_sp cpsr values lr prefix suffix first old_words
    publication frame Habsent Hswitch Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range Hpublication
    Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hsched_pre Hsave).
Qed.

