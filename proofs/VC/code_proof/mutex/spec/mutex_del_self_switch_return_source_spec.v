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
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
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
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_return_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A stale current-priority cache may request OSCtxSw while the selector
    chooses the SAME task. Use the actual outgoing Save/capture entry, then
    take it immediately at physical installation. The selected descriptor
    is thus the just-written one, including its masked CPSR and local
    saved-token/inside ownership. No foreign execution or future selection
    is assumed. The later C Restore uses its own cursor and LR and reaches
    Del's existing source return interface. *)
Lemma mutex_del_sched_self_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
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
  let current := os_sched_install_context call fragments call.(os_sched_call_stack) updated in
  let returned := kernel_selected_call suspended current in
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  os_sched_requests_switch state = true ->
  checkpoint.(SchedState).(highRdyTid) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
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
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
          suspended.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads suspended installed /\
        (forall restored,
          armv7a_task_restore_transition task_abi call suspended installed restored ->
          os_sched_source_switch_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi sg
            checkpoint call old_sp cpsr values lr suspended call.(os_sched_call_stack) suspended prefix_heap restored /\
          forall cursor restore_written middle final_cursor after,
          cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
          final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
          (mutex_del_source_return environment environment.(mutex_del_call_external)
             environment.(mutex_del_call_platform) sg call mask ** frame) after)).
Proof.
  intros environment critical arch save task_abi restore sg call mask state registers before final_registers
    acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame
    abi focus checkpoint fragments suspended updated current returned Habsent Hswitch Hselected Hreturn Hvalid_sr Hmask
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
  destruct (kernel_sched_save_capture_source _ _ _ abi critical arch save task_abi
    sg state call node mask focus old_sp cpsr values lr prefix suffix first old_words publication
    registers final_registers acquired before saved_heap (event_private_pool_rep sg state.(EventState) ** frame)
    Hswitch Hnonempty Hinput Hcovered Hsource Hreturn Hvalid_sr Hmask Howned Hsave)
    as [Hrun [Hacquired [prefix_heap [written [stored [Hprefix [Hwrites [Hload [Hstore
      [Hcovered_updated Hcapture_source]]]]]]]]]].
  fold checkpoint fragments suspended updated in Hstore, Hcovered_updated, Hcapture_source.
  pose proof (proj1 (kernel_call_save_uninterrupted_return_values arch registers state before
    final_registers acquired saved_heap Hrun)) as Hsaved_word.
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask)
    by (rewrite Hsaved_word; exact Hmask).
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hlookup : updated.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { unfold updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hpriority : checkpoint.(SchedState).(highRdyPrio) = Some node.(curPrio)).
  { unfold sched_high_ready_consistency in Hhigh.
    destruct checkpoint.(SchedState).(readyList) as [|head tail] eqn:Hlist.
    - exfalso; apply Hnonempty; congruence.
    - destruct Hhigh as [Hhead [high_node [Hget Hpriority]]].
      assert (head = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst head.
      change checkpoint.(TskState) with state.(TskState) in Hget.
      assert (high_node = node) by congruence; subst high_node; exact Hpriority. }
  assert (Hmember : In call.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)).
  { change (In call.(os_sched_call_stack).(stackLeaseSlot) checkpoint.(SchedState).(readyList)).
    unfold sched_high_ready_consistency in Hhigh.
    destruct checkpoint.(SchedState).(readyList) as [|head tail] eqn:Hlist.
    - exfalso; apply Hnonempty; congruence.
    - destruct Hhigh as [Hhead _].
      assert (head = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst head; left; reflexivity. }
  assert (Hcovered_current : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks updated.(TskState)
        (task_stack_park_fragments updated.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) fragments))
      call.(os_sched_call_stack)
      (task_stack_park_covers_active updated.(TskState) call.(os_sched_call_stack) fragments Hcovered_updated)). }
  assert (Hreachable_current : mutex_program_selected_reachable sg current).
  { eapply mutex_program_source_history_reachable; [exact Hreachable|].
    eapply mutex_program_task_fields_source with (tid := call.(os_sched_call_stack).(stackLeaseSlot))
      (old := node) (new := task_set_saved_sp node suspended.(armv7a_continuation_sp));
      [exact Hnode|reflexivity|reflexivity| |].
    - unfold current, os_sched_install_context, updated, os_sched_save_current_sp,
        checkpoint, os_sched_prefix_state; cbn [replace_SchedS TskState]; rewrite Hnode; reflexivity.
    - unfold current, os_sched_install_context, updated, os_sched_save_current_sp,
        checkpoint, os_sched_prefix_state; cbn [replace_SchedS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Hevents : current.(EventState) = state.(EventState)).
  { unfold current, os_sched_install_context, updated, os_sched_save_current_sp,
      checkpoint, os_sched_prefix_state; cbn [replace_SchedS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Htypes_current : mutex_del_private_types_non_mutex current.(EventState))
    by (rewrite Hevents; exact Htypes).
  split; [exact Hrun|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture_source captured Hcapture) as [Hmemory [Hsave_source Hcaptured]].
  assert (Hrestore_source : environment.(mutex_del_call_external).(os_sched_arch_restore_source)
    call.(os_sched_call_stack) suspended.(armv7a_continuation_sp) fragments).
  { match type of Hcaptured with ?P captured => assert (Hobserve : P |--
      coq_prop (environment.(mutex_del_call_external).(os_sched_arch_restore_source)
        call.(os_sched_call_stack) suspended.(armv7a_continuation_sp) fragments) && TT) end.
    { unfold kernel_saved_sched_call_entry at 1; destruct task_stack_key_eq_dec; [|contradiction].
      unfold kernel_saved_sched_call; Intros.
      sep_apply_l_atomic (armv7a_task_dormant_restore_source _ _ _ abi task_abi suspended).
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured)). }
  assert (Hdestination : os_sched_destination_binding environment.(mutex_del_call_external)
    call fragments updated call.(os_sched_call_stack) fragments).
  { unfold os_sched_destination_binding; split; [exact Hselected|].
    split.
    - exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)).
      exact (conj Hlookup (conj Hgen (conj Hpriority Hrestore_source))).
    - split.
      + exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)).
        split; [exact Hlookup|]. unfold task_stack_lease_matches_task; cbn [task_set_saved_sp taskID taskGeneration tcbStkPtr].
        exact (conj Hid (conj Hgen Hsp_range)).
      + apply task_stack_park_fragments_lookup. }
  destruct (kernel_saved_sched_call_install_resume_source _ _ _ abi critical task_abi sg call fragments updated
    call final_registers.(kernel_save_r0) state suspended fragments focus captured
    (event_private_pool_rep sg state.(EventState) ** frame)
    Hsaved Hdestination (Haddress _) Hcaptured)
    as [installed [Hinstall [Hreads [Hsome [Hreturned_source Hrestore]]]]].
  fold current returned in Hreturned_source, Hrestore.
  assert (Hsame : kernel_stack_call_same_call returned call).
  { unfold returned, kernel_selected_call; rewrite Hsome.
    unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hactive_key : task_stack_call_active_key call =
    Some (task_stack_key call.(os_sched_call_stack))).
  { unfold task_stack_call_active_key; rewrite Horigin; reflexivity. }
  exists installed; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Htask_restore.
  split.
  - exists written, stored, captured, captured, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcapture
      (conj Hhook_heap (conj Hhook_step (conj Hinstall Htask_restore))))))).
  - intros cursor restore_written middle final_cursor after Hr0 Hmask192 Hrestore_prefix Hrestore_suffix.
    destruct (Hrestore restored Htask_restore) as [Hresume [Hpc [Hcpsr192 [Hrestored_memory Hrestored]]]].
    assert (Hvalid_current : UCOS2_state_inv sg current).
    { match type of Hrestored with ?P restored => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
      { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve restored Hrestored)). }
    assert (Hstage_returned : mutex_del_call_stage returned current).
    { unfold mutex_del_call_stage; rewrite (proj1 Hreturned_source).
      split; [exact Hreturned_source|]. intros Henabled_current.
      pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid_current))))) as Hready_members.
      destruct (Hready_members _ Hmember) as [ready [Hready_node [Hrange Heffective]]].
      rewrite (proj2 (proj2 Hsame)); exists ready; auto. }
    match type of Hrestored with ?P restored => assert (Hrestore_input : P |--
      kernel_stack_call_masked abi mutex_del_stack_resources critical sg
        (task_stack_call_active_key call) returned final_registers.(kernel_save_r0) state current ** frame) end.
    { sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ abi current.(TskState) focus
        current.(TskState).(parkedTaskStacks)).
      unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
      rewrite Hactive_key, Hevents; entailer!. }
    destruct (kernel_saved_sched_call_return_source (mutex_del_runtime_sched_environment environment)
      mutex_del_stack_resources critical arch restore sg call returned state final_registers.(kernel_save_r0)
      state current cursor restored restore_written middle final_cursor after frame
      Hsame Hreturned_source Hr0 Hmask192 (Hrestore_input restored Hrestored) Hrestore_prefix Hrestore_suffix)
      as [Hreturn_run [Hreturn_lr [Hclosed_return Hsched_post]]].
    split; [exact Hreturn_run|]. split; [exact Hreturn_lr|].
    match type of Hclosed_return with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { cbn [mutex_del_runtime_sched_environment task_stack_call_continuations].
      unfold mutex_del_source_return, mutex_del_source_return_at, mutex_del_runtime_return_at.
      Exists returned current environment; unfold mutex_del_callsite_environment.
      rewrite Hsaved_mask; entailer!. }
    exact (Hclose after Hclosed_return).
Qed.
