Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_initial_wait_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One source consumer, on one succession of heaps: the scheduler's
    uninterrupted Save, C selector/profile writes, sixteen stack words,
    TCB-SP store, capture, install and first task entry.  The first task's
    ordinary zero-count SemPend path then uses the already proved return
    continuation, retaining the ORIGINAL TaskCreate focus and handles.

    The ready prefix describes this actual branch. Other legal ready
    orders, saved destinations and repeated/nested IRQs require their own
    source cases. Register/stack facts describe the present save; the
    no-kernel-write reference hook remains an explicit source boundary.
    No initial-frame shape, future destination, saved-SP invariant or
    future public postcondition is assumed by this consumer. *)
Lemma task_create_sched_initial_wait_source : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (entry_abi : Armv7aInitialEntryABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg source_publication publication_before original eid event timeout tail
  mask registers before final_registers acquired saved_heap
  old_sp cpsr values lr prefix suffix first old_words original_publication
  call_before region args task_return lower old_frame upper (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let published := task_create_stack_publication_state sg source_publication publication_before in
  let focus := armv7a_call_focus original lr lr in
  let checkpoint := os_sched_prefix_state published in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image original old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token final_registers.(kernel_save_r0) original.(os_sched_call_invocation)
         original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) published ** frame) in
  kernel_call_task_source original published ->
  published.(SchedState).(isRunning) = true ->
  os_sched_requests_switch published = true ->
  published.(SchedState).(readyList) = source_publication.(stack_publication_slot) ::
    original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  published.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  original.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region original.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range original.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    original.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range original.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened published.(TskState) original_publication
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values ->
  armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = original.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  mutex_query_lookup published eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  0 <= timeout < 4294967296 ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (os_sched_stack_pre environment kernel_program_inv sg original mask published ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) published before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers published before final_registers acquired saved_heap /\
  acquired = published /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      suspended.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi original suspended stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected node,
        os_sched_destination_binding environment.(task_stack_call_external) original fragments updated incoming resumed /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored, armv7a_task_restore_transition task_abi original selected installed restored ->
          os_sched_source_switch_execution environment.(task_stack_call_external)
            environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi sg
            checkpoint original old_sp cpsr values lr suspended incoming selected prefix_heap restored /\
          (os_sched_source_selected_post environment.(task_stack_call_external)
             environment.(task_stack_call_platform) environment.(task_stack_call_port) abi sg
             focus incoming selected node (os_sched_install_context original fragments incoming updated) **
           retained) restored /\
          (selected.(armv7a_continuation_call) = None ->
           (exists initial_lower initial_words initial_upper,
             selected.(armv7a_continuation_fragments) =
               task_stack_complete_fragments selected.(armv7a_continuation_stack).(stackLeaseRegion)
                 (initial_lower ++ initial_words ++ initial_upper) /\
             selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
               Zlength initial_lower + 16 + Zlength initial_upper /\
             Zlength initial_words = 16 /\
             task_stack_saved_pointer_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion)
               selected.(armv7a_continuation_sp) /\
             selected.(armv7a_continuation_sp) =
               selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionBase) +
                 Zlength initial_lower * sizeof(UINT) /\
             0 <= selected.(armv7a_continuation_sp) < 4294967296) /\
           task_create_initial_wait_continuation environment critical arch boundary save restore task_abi
             sg source_publication publication_before original suspended incoming selected eid event timeout
             final_registers.(kernel_save_r0) call_before region args task_return lower old_frame upper
             frame restored))).
Proof.
  intros environment critical arch boundary save restore task_abi entry_abi initial sg source_publication
    publication_before original eid event timeout tail mask registers before final_registers acquired saved_heap
    old_sp cpsr values lr prefix suffix first old_words original_publication call_before region args task_return
    lower old_frame upper frame abi published focus checkpoint fragments suspended updated retained
    Hordinary Hrunning Hswitch Hlist Habsent Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range
    Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Hlookup Hnonnull Hlayout Htimeout Haddress
    Hpre Hsave.
  destruct Hordinary as [Horigin [Hactive Hcurrent]].
  pose proof (proj2 (proj2 Hactive)) as Hlive.
  rewrite Horigin in Hlive, Hcurrent.
  destruct Hlive as [original_node [Hnode Hgen]].
  assert (Hsame : task_tcb_init_stack_same_call original original) by (repeat split; reflexivity).
  destruct (task_create_tcb_return_sched_masked_source environment critical arch save sg original
    original mask published registers before final_registers acquired saved_heap frame
    Hsame Hreturn Hvalid_sr Hmask Hpre Hsave) as [_ [Hsave_run [Hstate [Hr0 Hmasked]]]].
  split; [exact Hsave_run|]. split; [exact Hstate|]. subst acquired.
  assert (Hnonempty : published.(SchedState).(readyList) <> []) by (rewrite Hlist; discriminate).
  destruct (task_create_sched_masked_switch_prefix_source environment critical sg original
    final_registers.(kernel_save_r0) published published lr saved_heap frame
    Horigin Habsent Hnonempty Hswitch Hmasked)
    as [prefix_heap [Hprefix [Hhigh [_ Hprefix_owned]]]].
  assert (Hvalid_state : UCOS2_state_inv sg published).
  { match type of Hpre with ?P before => assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg published) && TT) end.
    { unfold os_sched_stack_pre, kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
      unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hpre)). }
  assert (Hid : original_node.(taskID) = original.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid_state)))) as Hactive_nodes.
    destruct Hactive_nodes as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hnode].
    apply Hdomain; eauto. }
  pose proof (proj1 (proj1 (os_sched_requests_switch_iff published) Hswitch)) as Henabled.
  assert (Hcheckpoint_current : checkpoint.(SchedState).(curTaskID) =
    Some original.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch; exact Hcurrent. }
  assert (Hcheckpoint_nonempty : checkpoint.(SchedState).(readyList) <> []).
  { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch; exact Hnonempty. }
  assert (Hcheckpoint_node : checkpoint.(TskState).(inUsedTaskStates)
    original.(os_sched_call_stack).(stackLeaseSlot) = Some original_node) by exact Hnode.
  match type of Hprefix_owned with ?P prefix_heap => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage checkpoint.(TskState)
      (Some (task_stack_key original.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) original 192 ** UCOS2_inv sg checkpoint **
     armv7a_task_call_stacks abi checkpoint.(TskState) focus checkpoint.(TskState).(parkedTaskStacks) **
     retained)) end.
  { unfold os_sched_source_switch_pre, retained; entailer!. }
  destruct (Hopen prefix_heap Hprefix_owned) as [Hcoverage Howned].
  destruct (armv7a_task_save_global_call _ _ _ abi task_abi sg checkpoint original_node original old_sp
    cpsr values lr prefix suffix first old_words focus retained prefix_heap Hcheckpoint_current Hnode Hid Hgen
    Habsent Hcoverage ltac:(intros; reflexivity) Hfragments Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp
    (Haddress _) Howned)
    as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  fold fragments suspended updated in Hstore, Hcovered, Hcapture.
  assert (Hsaved : os_sched_saved_stack_binding original fragments updated).
  { apply task_create_saved_context_binding with (node := original_node) (publication := original_publication);
      try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hhigh_after : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; rewrite Hcheckpoint_node; cbn [replace_TskS TskState SchedState].
    change (sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState)) in Hhigh.
    unfold sched_high_ready_consistency in *.
    destruct checkpoint.(SchedState).(readyList) as [|head rest] eqn:Hcheckpoint_list; [contradiction|].
    destruct Hhigh as [Hhigh [high [Hhigh_lookup Hpriority]]]; split; [exact Hhigh|].
    destruct (Z.eqb head original.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    - apply Z.eqb_eq in Heq; subst head.
      assert (high = original_node) by congruence; subst high.
      exists (task_set_saved_sp original_node suspended.(armv7a_continuation_sp)); split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - exists high; split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hhigh_lookup. }
  assert (Hactive_updated : task_invocation_active updated.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { unfold updated, os_sched_save_current_sp; rewrite Hcheckpoint_node; cbn [replace_TskS TskState].
    eapply task_set_saved_sp_preserves_invocation_active; eassumption. }
  assert (Hbinding : armv7a_continuation_binding suspended)
    by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hslice : armv7a_task_frame_slice suspended).
  { exists (task_stack_fragments_rep original.(os_sched_call_stack).(stackLeaseRegion) prefix **
      task_stack_fragments_rep original.(os_sched_call_stack).(stackLeaseRegion) suffix).
    unfold suspended, armv7a_task_save_image, armv7a_continuation_words; cbn.
    unfold fragments; rewrite Hsp; apply armv7a_task_frame_fragments_split. }
  assert (Hsuspended_mask : armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192).
  { unfold suspended, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hswitch_mask. }
  exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hmemory [Hsource Hcaptured_owned]].
  match type of Hcaptured_owned with ?P captured => assert (Horder : P |--
    UCOS2_inv sg updated **
    task_stack_fragments_rep original.(os_sched_call_stack).(stackLeaseRegion) fragments **
    armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key original.(os_sched_call_stack))
      (original.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi original ** retained)) by entailer! end.
  destruct (task_create_install_initial_wait_return_source environment critical arch boundary save restore
    task_abi entry_abi initial sg source_publication publication_before original original_node suspended
    eid event timeout tail final_registers.(kernel_save_r0) published call_before region args task_return
    lower old_frame upper frame captured Hrunning Hswitch Hlist Hnode Hgen Horigin Hbinding eq_refl Hslice
    Hsuspended_mask Hactive_updated Hsaved Hhigh_after Hcovered Hlookup Hnonnull Hlayout Htimeout Haddress
    (Horder captured Hcaptured_owned))
    as [incoming [resumed [installed [selected [node [Hdestination [Hselected_fragments [Hinstall
      [Hreads Hrestore_source]]]]]]]]].
  exists incoming, resumed, installed, selected, node.
  split; [exact Hdestination|]. split; [exact Hselected_fragments|]. split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Hrestore.
  split.
  - exists written, stored, captured, captured, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcaptured
      (conj Hhook_heap (conj Hhook_step (conj Hinstall Hrestore))))))).
  - exact (Hrestore_source restored Hrestore).
Qed.

