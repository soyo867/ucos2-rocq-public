Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_foreign_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** TCBInit's actual publication stores and final Restore produce the
    heap on which TaskCreate reads OSRunning. On its nonzero branch the
    retained caller stage yields current/ready/absent-key facts. Its
    registration comes from the earlier real Create entry and source
    transport, not from the CPU owner or a saved descriptor.

    The next actual Scheduler Save and selector then select a DIFFERENT
    task: the current-priority byte is supplied by the same caller stage,
    so the true switch guard cannot be the stale same-task-cache case.
    Physical install and TaskRestore retain this exact caller's new Save
    token and inside handle in the parked map. No original return, future
    selection, foreign API entry, or foreign invocation registration is
    inferred. The hook is the explicit no-write execution branch.

    TCB Restore and the later Scheduler/OSCtxSw call have separate actual
    cursors and LR values. The existing modular C boundaries connect the
    physical heaps; no equality between those distinct BL return sites is
    introduced. *)
Lemma task_create_tcb_publication_foreign_entry_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg publication state original entry call saved acquired before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let args := task_create_stack_publication_args publication in
  let published := task_create_stack_publication_state sg publication state in
  UCOS2_state_inv sg state ->
  task_create_stack_publication_input sg publication state ->
  task_create_source_entry sg publication.(stack_publication_args)
    publication.(stack_publication_name) original entry ->
  task_tcb_init_stack_same_call call original ->
  task_tcb_init_stack_source_preserved original entry state ->
  publication.(stack_publication_invocation) = call.(os_sched_call_invocation) ->
  publication.(stack_publication_origin) = call.(os_sched_call_origin) ->
  task_create_call_stage call state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg args state
     publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   armv7a_task_stack_continuations abi state.(TskState) state.(TskState).(parkedTaskStacks) **
   (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame)) before ->
  exists publication_heap,
    task_tcb_init_publication_tail_fragment sg args.(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before publication_heap /\
    kernel_client_step (task_create_stack_publication_client publication) sg state published /\
    task_create_call_stage call published /\
    (forall tcb_cursor tcb_written tcb_middle tcb_final returned_heap,
      tcb_cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask tcb_cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore tcb_cursor publication_heap tcb_written tcb_middle ->
      armv7a_restore_suffix_transition restore tcb_written tcb_middle tcb_final returned_heap ->
      kernel_call_restore_uninterrupted_execution arch tcb_cursor publication_heap tcb_final returned_heap /\
      tcb_final.(kernel_restore_return_word) = Some tcb_cursor.(kernel_restore_lr) /\
      uchar_load sg.(g_OSRunning) (task_create_stack_running published) returned_heap /\
      (forall registers final_registers sched_acquired saved_heap
        old_sp cpsr values lr prefix suffix first old_words owner_publication,
        task_create_stack_running published <> 0 ->
        os_sched_requests_switch published = true ->
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
        call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
        valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
        task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
          call.(os_sched_call_fragments) ->
        task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
        task_publication_happened state.(TskState) owner_publication
          call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
        List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
        Forall (fun value => 0 <= value < 4294967296) values ->
        armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
        old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
        (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) published returned_heap
          final_registers sched_acquired saved_heap ->
        let focus := armv7a_call_focus call lr lr in
        let checkpoint := os_sched_prefix_state published in
        let fragments := prefix ++ [(first, first + 16,
          map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
        let descriptor := armv7a_task_save_image call old_sp cpsr values lr fragments in
        let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
          descriptor.(armv7a_continuation_sp) in
        kernel_call_save_uninterrupted_execution arch registers published returned_heap
          final_registers sched_acquired saved_heap /\
        sched_acquired = published /\
        exists prefix_heap written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
            descriptor.(armv7a_continuation_sp)) written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi call descriptor stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists incoming resumed installed selected current_node,
              environment.(task_stack_call_external).(os_sched_arch_save_source)
                call descriptor.(armv7a_continuation_sp) fragments /\
              os_sched_destination_binding environment.(task_stack_call_external) call fragments updated incoming resumed /\
              task_stack_key incoming <> task_stack_key call.(os_sched_call_stack) /\
              selected.(armv7a_continuation_stack) = incoming /\
              selected.(armv7a_continuation_fragments) = resumed /\
              sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
                selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
                (task_stack_key call.(os_sched_call_stack)) = Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments) /\
              sched_current_ready_at (os_sched_install_context call fragments incoming updated).(TskState)
                (os_sched_install_context call fragments incoming updated).(SchedState) incoming.(stackLeaseSlot) current_node /\
              current_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
              task_stack_live_coverage (os_sched_install_context call fragments incoming updated).(TskState)
                (Some (task_stack_key incoming)) /\
              (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
              (forall restored,
                armv7a_task_restore_transition task_abi call selected installed restored ->
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi sg
                  checkpoint call old_sp cpsr values lr descriptor incoming selected prefix_heap restored /\
                armv7a_task_restored_source environment.(task_stack_call_external) selected /\
                (armv7a_task_restored_execution environment.(task_stack_call_external)
                   environment.(task_stack_call_platform) environment.(task_stack_call_port) abi selected **
                 kernel_program_inv sg (os_sched_install_context call fragments incoming updated) **
                 store_parked_continuations
                   (kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) published descriptor
                     (os_sched_install_context call fragments incoming updated).(TskState) focus)
                   (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks) ** frame) restored)))).
Proof.
  intros environment critical arch save restore task_abi initial sg publication state original entry call saved
    acquired before frame abi args published Hvalid Hpublication Hentry Hsame Htransport Hinvocation Hcall_origin
    Hstage Hcoverage Hpriority Hpointer Hpre.
  destruct (task_create_tcb_publication_world_source environment critical sg publication state call saved acquired
    before frame Hvalid Hpublication Hstage Hcoverage Hpriority Hpointer Hpre)
    as [publication_heap [Hstores [Hstep [Hstage_published Hmasked]]]].
  fold published in Hstep, Hstage_published, Hmasked.
  exists publication_heap; split; [exact Hstores|]. split; [exact Hstep|]. split; [exact Hstage_published|].
  intros tcb_cursor tcb_written tcb_middle tcb_final returned_heap Hr0 Hmask Hprefix Hsuffix.
  match type of Hmasked with ?P publication_heap => assert (Hopen : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_stack_inv abi kernel_program_inv sg (task_stack_call_active_key call) published ** frame))
    by (unfold kernel_stack_call_masked; entailer!) end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call saved acquired
    tcb_cursor publication_heap tcb_written tcb_middle tcb_final returned_heap _ Hr0 Hmask
    (Hopen publication_heap Hmasked) Hprefix Hsuffix) as [Htcb_run [Htcb_lr [Hmemory Howned]]].
  assert (Hclosed : (kernel_stack_call_closed abi kernel_program_inv sg (task_stack_call_active_key call)
    call (armv7a_irq_fiq_mask saved) published ** frame) returned_heap).
  { match type of Howned with ?P returned_heap => match goal with |- ?Q returned_heap =>
      assert (Hclose : P |-- Q) by (unfold kernel_stack_call_closed; entailer!) end end.
    exact (Hclose returned_heap Howned). }
  assert (Hload : uchar_load sg.(g_OSRunning) (task_create_stack_running published) returned_heap).
  { match type of Hclosed with ?P returned_heap => assert (Hread : P |--
      sg.(g_OSRunning) # UChar |-> task_create_stack_running published ** TT) end.
    { unfold kernel_stack_call_closed, kernel_stack_inv; Intros.
      rewrite kernel_program_inv_split_unmap, UCOS2_inv_split_running.
      unfold task_create_stack_running; Intros; entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hread returned_heap Hclosed). }
  split; [exact Htcb_run|]. split; [exact Htcb_lr|]. split; [exact Hload|].
  intros registers final_registers sched_acquired saved_heap old_sp cpsr values lr prefix suffix first old_words
    owner_publication Hnonzero Hswitch Hreturn Hvalid_sr Hsaved_mask Hfragments Hregion Hgeometry Hsp_range
    Howner_publication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hsave
    focus checkpoint fragments descriptor updated.
  assert (Hrunning : published.(SchedState).(isRunning) = true).
  { unfold task_create_stack_running in Hnonzero.
    destruct published.(SchedState).(isRunning); [reflexivity|contradiction]. }
  pose proof (proj1 (os_sched_requests_switch_iff published) Hswitch) as [Henabled Hprio_ne].
  destruct (task_create_call_stage_selection_ready call published Hstage_published Hrunning Henabled)
    as [Horigin [Habsent [node [Hcurrent_ready Hgen]]]].
  pose proof Hcurrent_ready as [Hnode [Hcurrent [Hcurrent_priority [Hin Heffective]]]].
  assert (Hentry_running : entry.(SchedState).(isRunning) = true).
  { pose proof (proj1 (proj2 Hentry)) as Hentry_origin.
    unfold task_create_call_origin in Hentry_origin.
    rewrite <- (proj1 (proj2 Hsame)), Horigin in Hentry_origin; exact (proj1 Hentry_origin). }
  assert (Hsource : kernel_call_task_source call published).
  { eapply task_create_stack_publication_preserves_call_source; [exact Hvalid|exact Hpublication|].
    apply (proj2 (task_tcb_init_stack_same_call_source_iff call original state Hsame)).
    apply Htransport; eapply task_create_source_entry_running_source; eassumption. }
  assert (Hnonempty : published.(SchedState).(readyList) <> []).
  { intro Hempty; rewrite Hempty in Hin; contradiction. }
  assert (Hvalid_published : UCOS2_state_inv sg published).
  { eapply task_create_stack_publication_preserves_validity; [exact Hvalid|exact Hstep]. }
  assert (Hcovered : task_stack_live_coverage published.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hclosed with ?P returned_heap => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage published.(TskState) (task_stack_call_active_key call)) && TT) end.
    { unfold kernel_stack_call_closed, kernel_stack_inv; entailer!; intros ? ?; exact I. }
    pose proof (proj1 (Hobserve returned_heap Hclosed)) as Hcovered.
    unfold task_stack_call_active_key in Hcovered; rewrite Horigin in Hcovered; exact Hcovered. }
  assert (Hhigh : sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState)).
  { apply os_sched_ready_checkpoint_high_consistency with (sg := sg);
      [exact (proj1 (proj1 (proj2 (proj2 Hvalid_published))))|exact Henabled]. }
  assert (Hforeign : checkpoint.(SchedState).(highRdyTid) <>
    Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { intro Hequal; apply Hprio_ne.
    change ((os_sched_ready_checkpoint published).(highRdyTid) =
      Some call.(os_sched_call_stack).(stackLeaseSlot)) in Hequal.
    unfold sched_high_ready_consistency in Hhigh.
    change (sched_high_ready_consistency published.(TskState) (os_sched_ready_checkpoint published)) in Hhigh.
    unfold sched_high_ready_consistency in Hhigh.
    rewrite (proj1 (os_sched_ready_checkpoint_frame published)) in Hhigh.
    destruct published.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhead Hhigh_node].
    assert (Hslot : head = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
    rewrite (sched_selected_priority_eq_head sg published.(TskState) published.(SchedState)
      head tail node (proj1 (proj1 Hvalid_published))
      (proj1 (proj1 (proj2 (proj2 Hvalid_published)))) Hlist ltac:(rewrite Hslot; exact Hnode)).
    rewrite Hcurrent_priority; reflexivity. }
  assert (Hid : node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid_published)))) as Hactive_nodes.
    destruct Hactive_nodes as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hnode].
    apply Hdomain; eauto. }
  assert (Hpublication_after : task_publication_happened checkpoint.(TskState) owner_publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration)).
  { change (task_publication_happened (task_commit state.(TskState) args.(initPrio)
      publication.(stack_publication_invocation)
      (task_tcb_init_commit_node args publication.(stack_publication_acquired)
        publication.(stack_publication_slot) publication.(stack_publication_image))) owner_publication
      call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration)).
    unfold task_publication_happened; simpl.
    right; exact Howner_publication. }
  assert (Hcheckpoint_current : checkpoint.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { change ((os_sched_ready_checkpoint published).(curTaskID) =
      Some call.(os_sched_call_stack).(stackLeaseSlot)).
    rewrite (proj1 (proj2 (os_sched_ready_checkpoint_frame published))); exact Hcurrent. }
  assert (Hcheckpoint_nonempty : checkpoint.(SchedState).(readyList) <> []).
  { change ((os_sched_ready_checkpoint published).(readyList) <> []).
    rewrite (proj1 (os_sched_ready_checkpoint_frame published)); exact Hnonempty. }
  assert (Hlive_input : os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus owner_publication).
  { unfold os_sched_source_live_save_input, focus.
    repeat first [assumption | reflexivity | split | intro]. }
  match type of Hclosed with ?P returned_heap => assert (Hshared : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      call (armv7a_irq_fiq_mask saved) ** kernel_program_inv sg published **
    armv7a_task_call_stacks abi published.(TskState) focus published.(TskState).(parkedTaskStacks) ** frame) end.
  { unfold kernel_stack_call_closed, kernel_stack_inv; Intros.
    sep_apply_l_atomic (armv7a_task_call_stacks_absent _ _ _ abi published.(TskState) focus
      published.(TskState).(parkedTaskStacks) Habsent); entailer!. }
  destruct (kernel_sched_save_foreign_source _ _ _ abi critical arch save task_abi initial sg published call node
    (armv7a_irq_fiq_mask saved) focus old_sp cpsr values lr prefix suffix first old_words owner_publication
    registers final_registers sched_acquired returned_heap saved_heap frame Hswitch Hnonempty Hforeign
    Hlive_input Hcovered Hsource Hreturn Hvalid_sr Hsaved_mask (Hshared returned_heap Hclosed) Hsave)
    as [Hsave_run [Hacquired [prefix_heap [written [stored [Hselector [Hwrites [Hcur_load [Hsp_store Hcapture]]]]]]]]].
  fold checkpoint fragments descriptor updated in Hcapture, Hsp_store.
  split; [exact Hsave_run|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hselector|]. split; [exact Hwrites|].
  split; [exact Hcur_load|]. split; [exact Hsp_store|].
  intros captured hooked Hcapture_run Hhook_heap Hhook_step.
  destruct (Hcapture captured hooked Hcapture_run Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current_node [Harch_save [Hdestination [Hother [Hlease
      [Hselected_fragments [Hinstall [Hreads [Horiginal [Hselected_ready [Hselected_gen
      [Hselected_coverage [Hfocus_kept [Hinitial Hrestore]]]]]]]]]]]]]]]]]].
  exists incoming, resumed, installed, selected, current_node.
  exact (conj Harch_save (conj Hdestination (conj Hother (conj Hlease (conj Hselected_fragments
    (conj Hinstall (conj Hreads (conj Horiginal (conj Hselected_ready (conj Hselected_gen
    (conj Hselected_coverage (conj Hinitial Hrestore)))))))))))).
Qed.
