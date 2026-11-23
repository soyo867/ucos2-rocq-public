Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_wake_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** An actual ordinary API-return/next-entry source event, followed by the
    literal SemPost type read, its uninterrupted first Save and group read.
    The selected foreign task is not silently declared to have called Post:
    [kernel_sequential_call_source] is the linked program's observed boundary.
    Registration changes only ghost call identity; the focused pending owner
    and its bytes stay in the SAME world. The result is EventTaskRdy's PRE,
    not an assumed wake or a made-up post-state. *)
Lemma sem_pend_post_entry_waiter_pre : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg previous original focus mask state eid event before entered registers
  final_registers acquired after (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
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
    registers final_registers acquired after frame abi call entry Hlive Hcoverage Hactive Hlookup Htype
    Hnonnull Hgroup Hlayout Hpre Hboundary Hreturn Hcpsr Hmask Hsave.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  match type of Hpre with ?P before => assert (Hopen : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      previous mask ** (kernel_program_inv sg state **
    armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))
    by entailer! end.
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before entered _ Hboundary (Hopen before Hpre))
    as [Hmemory Hentered].
  fold call in Hentered.
  assert (Hactive_entry : task_invocation_active entry.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { apply task_begin_invocation_preserves_invocation_active; [|exact Hactive].
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj2 Hvalid))))))). }
  assert (Hcovered : task_stack_live_coverage entry.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))) by exact Hcoverage.
  assert (Hentry_group : sem_post_group entry event <> 0).
  { unfold sem_post_group in *.
    rewrite <- (proj1 (event_wait_encoding_priority_ext event.(waitList) state.(TskState)
      entry.(TskState) ltac:(intros; reflexivity))); exact Hgroup. }
  match type of Hentered with ?P entered => assert (Hregister : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      call mask ** (kernel_program_inv sg entry **
    armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite !kernel_program_inv_split_unmap.
    sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state previous.(os_sched_call_origin) Hlive).
    change (armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks)) with
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks)).
    entailer!. }
  pose proof (Hregister entered Hentered) as Hentry.
  assert (Htype_read : uchar_load (event_addr sg eid + OSEventType_off) 3 entered).
  { match type of Hentry with ?P entered => assert (Hcell : P |--
      (event_addr sg eid + OSEventType_off) # UChar |-> 3 ** TT) end.
    { rewrite kernel_program_inv_split_unmap.
      sep_apply_l_atomic (sem_post_field_split_full sg entry eid event EventTypeField Hlookup ltac:(simpl; tauto)).
      cbn [event_cell event_image event_field_offset]; rewrite Htype; cbn [encode_event_type].
      unfold OSEventType_off; entailer!; intros ? ?; exact I. }
    exact (framed_uchar_store_load _ _ _ _ (Hcell entered Hentry)). }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  rewrite <- Hmask in Hentry.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) entry entered final_registers acquired after _
    Hsaved Hentry Hsave) as [Hstate [Hmemory_after [Hlr [Hr0 Hafter]]]].
  split; [exact Htype_read|]. split.
  - unfold kernel_call_save_uninterrupted_execution; econstructor.
    + constructor; [exact Hreturn|reflexivity].
    + exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hstate|]. subst acquired.
    assert (Hentry_valid : UCOS2_state_inv sg entry).
    { match type of Hafter with ?P after => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg entry) && TT) end.
      { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve after Hafter)). }
    split; [exact Hentry_valid|].
    split.
    + match type of Hafter with ?P after => assert (Hcell : P |--
        (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group entry event ** TT) end.
      { rewrite kernel_program_inv_split_unmap.
        sep_apply_l_atomic (sem_post_field_split_full sg entry eid event EventGrpField Hlookup ltac:(simpl; tauto)).
        cbn [event_cell event_image event_field_offset]; unfold sem_post_group, OSEventGrp_off; entailer!; intros ? ?; exact I. }
      exact (framed_uchar_store_load _ _ _ _ (Hcell after Hafter)).
    + split; [exact Hactive_entry|]. split; [exact Hcovered|].
      match type of Hafter with ?P after => match goal with |- ?Q => assert (Hsplit : P |--
        EX tid old, coq_prop (event_task_rdy_entry sg entry.(TskState) eid event tid old) &&
        (event_task_rdy_pre sg entry.(TskState) eid event tid old 1 0
          (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
          (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
        (critical_region_masked environment.(task_stack_call_platform) critical sg
          call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
        os_sched_context_resources environment.(task_stack_call_external) call **
        sem_post_wake_frame sg entry eid tid **
        armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame))) end end.
      { rewrite kernel_program_inv_split_unmap.
        eapply derivable1_trans with (y := (UCOS2_inv sg entry ** unmap_table_rep sg) **
          (critical_region_masked environment.(task_stack_call_platform) critical sg
            call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
           os_sched_context_resources environment.(task_stack_call_external) call **
           armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame));
          [entailer!|].
        sep_apply_l_atomic (sem_post_wake_split_full sg entry eid event Hentry_valid Hlookup Htype Hentry_group Hlayout).
        Intros tid old; Exists tid old; entailer!. }
      exact (Hsplit after Hafter).
Qed.

(** The first scheduler call after an actual wait. The outgoing task is
    deliberately NOT ready. Its real Save, selector, sixteen stack stores,
    TCB-SP store and install/take establish the parked pending invocation.
    The selected task is only a foreign destination, not yet a SemPost
    entry. Its subsequent ordinary entry must consume the source boundary
    above. Absence and stack geometry describe this current source cut;
    they are not quantified future acquire-safety requirements. *)
Lemma sem_pend_wait_sched_switch_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg call mask state eid node registers before final_registers acquired saved_heap
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state ** frame) in
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration) node ->
  ~ In call.(os_sched_call_stack).(stackLeaseSlot) state.(SchedState).(readyList) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  state.(SchedState).(readyList) <> [] -> os_sched_requests_switch state = true ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values ->
  armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (os_sched_stack_pre environment kernel_program_inv sg call mask state ** frame) before ->
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
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists incoming selected installed current,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          let foreign_state := os_sched_install_context call fragments incoming updated in
          os_sched_source_switch_execution environment.(task_stack_call_external) environment.(task_stack_call_platform)
            environment.(task_stack_call_port) abi task_abi sg checkpoint call old_sp cpsr values lr
            suspended incoming selected prefix_heap restored /\
          incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot) /\
          foreign_state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
            Some (task_set_saved_sp node suspended.(armv7a_continuation_sp)) /\
          sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration)
            (task_set_saved_sp node suspended.(armv7a_continuation_sp)) /\
          task_invocation_active foreign_state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
          task_saved_pointer_at foreign_state call.(os_sched_call_stack) suspended.(armv7a_continuation_sp) /\
          foreign_state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
            Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments) /\
          armv7a_task_restored_source environment.(task_stack_call_external) selected /\
          (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
             environment.(task_stack_call_port) abi sg focus incoming selected current foreign_state ** retained) restored)).
Proof.
  intros environment critical arch save task_abi initial sg call mask state eid node registers before
    final_registers acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame
    abi focus checkpoint fragments suspended updated retained Hsource Hnode Hwait Hblocked Habsent Hnonempty Hswitch
    Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges
    Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave.
  pose proof Hsource as [Horigin [Hactive Hcurrent]].
  assert (Hgen : node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration)) by exact (proj1 Hwait).
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold os_sched_stack_pre, kernel_stack_call_closed, kernel_stack_inv.
      rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  assert (Hid : node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hlinks.
    destruct Hlinks as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hnode].
    apply Hdomain; eauto. }
  destruct (task_create_tcb_return_sched_masked_source environment critical arch save sg call call mask state
    registers before final_registers acquired saved_heap frame ltac:(repeat split; reflexivity)
    Hreturn Hvalid_sr Hmask Hpre Hsave) as [_ [Hrun [Hstate [Hr0 Hmasked]]]].
  split; [exact Hrun|]. split; [exact Hstate|]. subst acquired.
  destruct (task_create_sched_masked_switch_prefix_source environment critical sg call
    final_registers.(kernel_save_r0) state state lr saved_heap frame Horigin Habsent Hnonempty Hswitch Hmasked)
    as [prefix_heap [Hprefix [Hhigh [_ Hprefix_owned]]]].
  assert (Henabled : os_sched_selection_enabled state = true)
    by exact (proj1 (proj1 (os_sched_requests_switch_iff state) Hswitch)).
  unfold task_execution_current in Hcurrent; rewrite Horigin in Hcurrent.
  assert (Hinput : os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input, focus.
    assert (Hready : checkpoint.(SchedState).(readyList) = state.(SchedState).(readyList))
      by exact (proj1 (os_sched_ready_checkpoint_frame state)).
    assert (Hcur : checkpoint.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
    { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch; exact Hcurrent. }
    rewrite Hready. repeat first [assumption | reflexivity | split | intro]. }
  match type of Hprefix_owned with ?P prefix_heap => assert (Horder : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg call focus checkpoint ** retained)
    by (unfold retained; entailer!) end.
  destruct (os_sched_source_live_switch_destination_resources _ _ _ abi task_abi initial sg checkpoint node call
    old_sp cpsr values lr prefix suffix first old_words focus publication retained prefix_heap Hinput
    (Horder prefix_heap Hprefix_owned)) as [written [stored [Hwrites [Hload [Hstore Hselected]]]]].
  exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselected captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current [Harch [Hdestination [Hselected_fragments
      [Hinstall [Hreads [Hpending Hrestore]]]]]]]]]]].
  exists incoming, selected, installed, current; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Hrestored; cbv zeta.
  destruct (Hrestore restored Hrestored) as [Hexecution [Hrestored_source Howned]].
  set (foreign_state := os_sched_install_context call fragments incoming updated) in *.
  fold abi focus checkpoint fragments suspended updated retained in Howned, Hexecution.
  assert (Hready : sched_current_ready_at foreign_state.(TskState) foreign_state.(SchedState)
    incoming.(stackLeaseSlot) current).
  { match type of Howned with ?P restored => assert (Hobserve : P |-- coq_prop
      (sched_current_ready_at foreign_state.(TskState) foreign_state.(SchedState)
        incoming.(stackLeaseSlot) current) && TT) end.
    { unfold os_sched_source_selected_post; Intros; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve restored Howned)). }
  assert (Hready_list : foreign_state.(SchedState).(readyList) = state.(SchedState).(readyList)).
  { unfold foreign_state, updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; change (checkpoint.(SchedState).(readyList) = state.(SchedState).(readyList)).
    exact (proj1 (os_sched_ready_checkpoint_frame state)). }
  assert (Hother : incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot)).
  { destruct Hready as [_ [_ [_ [Hin _]]]]; rewrite Hready_list in Hin; intro Heq; rewrite Heq in Hin; contradiction. }
  assert (Hlookup : foreign_state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { unfold foreign_state, updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; cbn [os_sched_install_context replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hwait_after : sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration)
    (task_set_saved_sp node suspended.(armv7a_continuation_sp))) by exact Hwait.
  assert (Hactive_after : task_invocation_active foreign_state.(TskState)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { unfold foreign_state, updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; change (task_invocation_active (glob_task_set_usedtask state.(TskState)
      call.(os_sched_call_stack).(stackLeaseSlot) (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
      call.(os_sched_call_invocation) call.(os_sched_call_origin)).
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive]. }
  assert (Hpointer : task_saved_pointer_at foreign_state call.(os_sched_call_stack) suspended.(armv7a_continuation_sp)).
  { exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)); repeat split; assumption. }
  assert (Hparked : foreign_state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments)).
  { change ((task_stack_take (task_stack_park_fragments updated.(TskState).(parkedTaskStacks)
      call.(os_sched_call_stack) fragments) incoming) (task_stack_key call.(os_sched_call_stack)) =
      Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments)).
    rewrite task_stack_take_lookup_other; [apply task_stack_park_fragments_lookup|].
    unfold task_stack_key; intro Heq; injection Heq; congruence. }
  exact (conj Hexecution (conj Hother (conj Hlookup (conj Hwait_after (conj Hactive_after
    (conj Hpointer (conj Hparked (conj Hrestored_source Howned)))))))).
Qed.

(** Consume the actual foreign selected owner, finish its matching saved
    ordinary call, then observe the linked program's next SemPost entry.
    The two saved-mask/inside owners are distinct: the foreign one is used
    by this Restore, while the original Pend's owner stays in [frame]. *)
Lemma sem_pend_selected_post_entry_waiter_pre : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original focus incoming selected node state previous saved previous_entry eid event
  before cursor written middle final_cursor released entered registers final_registers acquired after (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let resumed := armv7a_continuation_resumed_call selected previous in
  let call := kernel_sequential_call resumed state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation resumed.(os_sched_call_origin) state.(TskState)) state in
  selected.(armv7a_continuation_call) = Some previous ->
  previous.(os_sched_call_origin) = RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  sem_post_lookup state eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_addr sg eid <> 0 -> sem_post_group state event <> 0 -> event_object_layout_prop sg eid ->
  (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg focus incoming selected node state ** unmap_table_rep sg **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved previous.(os_sched_call_invocation) previous.(os_sched_call_origin)) **
    critical_region_inside critical sg previous.(os_sched_call_invocation) previous_entry ** frame)) before ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  kernel_sequential_call_source boundary resumed state.(TskState).(taskLifecycle).(taskNextInvocation) released entered ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry entered final_registers acquired after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
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
  intros environment critical arch boundary restore save sg original focus incoming selected node state previous saved
    previous_entry eid event before cursor written middle final_cursor released entered registers final_registers
    acquired after frame abi resumed call entry Hcall Horigin Hselected_mask Hactive Hlookup Htype Hnonnull Hgroup
    Hlayout Hpre Hr0 Hmask Hprefix Hsuffix Hboundary Hreturn Hcpsr Hnextmask Hsave.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (selected.(armv7a_continuation_stack) = incoming /\
      sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node /\
      node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
      task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       resumed.(os_sched_call_invocation) resumed.(os_sched_call_origin) saved previous_entry **
     os_sched_context_resources environment.(task_stack_call_external) resumed **
     (kernel_program_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
       state.(TskState).(parkedTaskStacks) ** frame))) end.
  { unfold os_sched_source_selected_post; Intros.
    unfold armv7a_task_restored_execution; rewrite Hcall, Hselected_mask.
    unfold critical_region_masked, kernel_call_execution_owned.
    rewrite kernel_program_inv_split_unmap; unfold resumed; cbn [armv7a_continuation_resumed_call
      os_sched_call_invocation os_sched_call_origin]; entailer!. }
  destruct (Hopen before Hpre) as [[Hlease [Hready [Hgen Hcoverage]]] Howned].
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg resumed saved
    previous_entry cursor before written middle final_cursor released _ Hr0 Hmask Howned Hprefix Hsuffix)
    as [Hrestore [Hword [Hmemory Hreleased]]].
  assert (Hlive : task_invocation_origin_live state.(TskState) resumed.(os_sched_call_origin)).
  { unfold resumed; cbn [armv7a_continuation_resumed_call os_sched_call_origin]; rewrite Horigin.
    exists node; split; [exact (proj1 Hready)|exact Hgen]. }
  assert (Hcovered : task_stack_live_coverage state.(TskState)
    (Some (task_stack_key resumed.(os_sched_call_stack)))).
  { unfold resumed; cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease; exact Hcoverage. }
  match type of Hreleased with ?P released => assert (Horder : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      resumed (armv7a_irq_fiq_mask saved) ** kernel_program_inv sg state **
    armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)
    by entailer! end.
  split; [exact Hrestore|].
  exact (sem_pend_post_entry_waiter_pre environment critical arch boundary save sg resumed original focus
    (armv7a_irq_fiq_mask saved) state eid event released entered registers final_registers acquired after frame
    Hlive Hcovered Hactive Hlookup Htype Hnonnull Hgroup Hlayout (Horder released Hreleased) Hboundary
    Hreturn Hcpsr Hnextmask Hsave).
Qed.


(** This is a modular call composition, not an assumption that a wake has
    already happened. The actual selected/Restore/next-entry/Save prefix
    establishes EventTaskRdy's PRE on [after]. Its established callee POST
    on [wake_heap], with precisely the same frame, is consumed immediately
    by the adopted Post-to-original-return source. The selected waiter and
    subsequent switch are explicit guards of this finite successful branch. *)
Lemma sem_pend_selected_post_wake_return_source : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg original suspended incoming selected node state previous saved previous_entry eid event
  waiting original_saved original_entry perr
  before cursor written middle final_cursor released entered registers final_registers acquired after (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let resumed := armv7a_continuation_resumed_call selected previous in
  let call := kernel_sequential_call resumed state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation resumed.(os_sched_call_origin) state.(TskState)) state in
  let retained := interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry **
    (perr # UChar |->_ ** frame) in
  selected.(armv7a_continuation_call) = Some previous ->
  previous.(os_sched_call_origin) = RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  sem_post_lookup state eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_addr sg eid <> 0 -> sem_post_group state event <> 0 -> event_object_layout_prop sg eid ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_saved_pointer_at state original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg focus incoming selected node state ** unmap_table_rep sg **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved previous.(os_sched_call_invocation) previous.(os_sched_call_origin)) **
    critical_region_inside critical sg previous.(os_sched_call_invocation) previous_entry ** retained)) before ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  kernel_sequential_call_source boundary resumed state.(TskState).(taskLifecycle).(taskNextInvocation) released entered ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry entered final_registers acquired after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered /\
  kernel_call_save_uninterrupted_execution arch registers entry entered final_registers acquired after /\
  acquired = entry /\
  uchar_load (event_addr sg eid + OSEventGrp_off) (sem_post_group entry event) after /\
  exists tid old,
    event_task_rdy_entry sg entry.(TskState) eid event tid old /\
    (event_task_rdy_pre sg entry.(TskState) eid event tid old 1 0
       (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
       (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     (critical_region_masked environment.(task_stack_call_platform) critical sg
        call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
      os_sched_context_resources environment.(task_stack_call_external) call **
      sem_post_wake_frame sg entry eid tid **
      armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** retained)) after /\
    (forall priority wake_heap post_cursor post_written post_middle post_final_cursor post_released
      sched_registers sched_final_registers sched_acquired sched_saved_heap
      outgoing old_sp cpsr values lr prefix suffix first old_words publication,
      let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
      let next := os_sched_prefix_state checkpoint in
      let fragments := prefix ++ [(first, first + 16,
        map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
      tid = original.(os_sched_call_stack).(stackLeaseSlot) ->
      os_sched_requests_switch checkpoint = true ->
      hd_error checkpoint.(SchedState).(readyList) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
      os_sched_source_live_save_input sg next outgoing call old_sp cpsr values lr
        prefix suffix first old_words focus publication ->
      (event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
         (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
         (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
       (critical_region_masked environment.(task_stack_call_platform) critical sg
          call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
        os_sched_context_resources environment.(task_stack_call_external) call **
        sem_post_wake_frame sg entry eid tid **
        armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** retained)) wake_heap ->
      post_cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask post_cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore post_cursor wake_heap post_written post_middle ->
      armv7a_restore_suffix_transition restore post_written post_middle post_final_cursor post_released ->
      sched_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr sched_registers.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask sched_registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask final_registers.(kernel_save_r0) ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr sched_registers) checkpoint post_released
        sched_final_registers sched_acquired sched_saved_heap ->
      kernel_call_restore_uninterrupted_execution arch post_cursor wake_heap post_final_cursor post_released /\
      kernel_call_save_uninterrupted_execution arch sched_registers checkpoint post_released
        sched_final_registers sched_acquired sched_saved_heap /\
      sched_acquired = checkpoint /\
      exists prefix_heap current,
        os_sched_source_switch_prefix_execution sg sched_saved_heap prefix_heap /\ current.(statPend) = PendOK /\
        sem_pend_live_switch_stack_return environment critical arch task_abi restore save sg next call old_sp cpsr
          values lr fragments original original_saved eid current perr prefix_heap
          (interrupt_platform_saved environment.(task_stack_call_platform)
             (save_token sched_final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
           critical_region_inside critical sg call.(os_sched_call_invocation) checkpoint ** frame)).
Proof.
  intros environment critical arch boundary restore save task_abi sg original suspended incoming selected node state
    previous saved previous_entry eid event waiting original_saved original_entry perr before cursor written middle
    final_cursor released entered registers final_registers acquired after frame abi focus resumed call entry retained
    Hcall Horigin Hselected_mask Hactive Hlookup Htype Hnonnull Hgroup Hlayout Hwaiting Hwait Hpointer Hparked
    Horiginal_origin Hbinding Horiginal_call Hslice Horiginal_mask Hpre Hr0 Hmask Hprefix Hsuffix Hboundary
    Hreturn Hcpsr Hnextmask Hsave.
  destruct (sem_pend_selected_post_entry_waiter_pre environment critical arch boundary restore save sg original
    focus incoming selected node state previous saved previous_entry eid event before cursor written middle
    final_cursor released entered registers final_registers acquired after retained Hcall Horigin Hselected_mask
    Hactive Hlookup Htype Hnonnull Hgroup Hlayout Hpre Hr0 Hmask Hprefix Hsuffix Hboundary Hreturn Hcpsr
    Hnextmask Hsave) as [Hrestore_run [Htype_read [Hsave_run [Hacquired [Hvalid [Hgroup_read [Hactive_entry
      [Hcoverage [tid [old [Hentry Hraw_pre]]]]]]]]]]].
  split; [exact Hrestore_run|]. split; [exact Htype_read|]. split; [exact Hsave_run|].
  split; [exact Hacquired|]. split; [exact Hgroup_read|].
  exists tid, old; split; [exact Hentry|]. split; [exact Hraw_pre|].
  intros priority wake_heap post_cursor post_written post_middle post_final_cursor post_released
    sched_registers sched_final_registers sched_acquired sched_saved_heap outgoing old_sp cpsr values lr
    prefix suffix first old_words publication checkpoint next fragments Hwoken Hswitch Hhead Hlive Hpost
    Hpost_r0 Hpost_mask Hpost_prefix Hpost_suffix Hsched_return Hsched_cpsr Hsched_mask Hsched_save.
  eapply sem_pend_post_wake_original_return_source with (entry := entry) (waiting := waiting)
    (old := old) (event := event) (tid := tid) (priority := priority) (suspended := suspended)
    (saved := final_registers.(kernel_save_r0)) (original_entry := original_entry)
    (node := outgoing) (old_words := old_words) (publication := publication);
    try eassumption.
  match type of Hpost with ?P wake_heap => match goal with |- ?Q wake_heap =>
      assert (Horder : P |-- Q) by (unfold retained; entailer!) end end.
  exact (Horder wake_heap Hpost).
Qed.

(** The first switch owns the selected CPU and the original pending
    call. This continuation consumes that SAME owner after the surrounding
    frame is split into the previously suspended foreign call's matching
    mask/inside handles and the original perr cell. Frame splitting is a
    separation entailment, not a source-effect or future-safety assumption. *)
Definition sem_pend_selected_post_wake_continuation
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext) (suspended : Armv7aContinuation)
  (incoming : TaskStackLease) (selected : Armv7aContinuation) (node : TaskAbstractState)
  (state : UCOS2_Verify_State) (eid : EventID) (waiting : TaskAbstractState)
  (original_saved : Z) (original_entry : UCOS2_Verify_State)
  (before : model) (outside : Assertion) : Prop :=
  forall arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  previous saved previous_entry event perr (rest : Assertion)
  cursor written middle final_cursor released entered registers final_registers acquired after,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let resumed := armv7a_continuation_resumed_call selected previous in
  let call := kernel_sequential_call resumed state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation resumed.(os_sched_call_origin) state.(TskState)) state in
  let retained := interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry **
    (perr # UChar |->_ ** rest) in
  selected.(armv7a_continuation_call) = Some previous ->
  previous.(os_sched_call_origin) = RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 ->
  sem_post_lookup state eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_addr sg eid <> 0 -> sem_post_group state event <> 0 -> event_object_layout_prop sg eid ->
  outside |-- interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved previous.(os_sched_call_invocation) previous.(os_sched_call_origin)) **
    critical_region_inside critical sg previous.(os_sched_call_invocation) previous_entry **
    (perr # UChar |->_ ** rest) ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  kernel_sequential_call_source boundary resumed state.(TskState).(taskLifecycle).(taskNextInvocation) released entered ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry entered final_registers acquired after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered /\
  kernel_call_save_uninterrupted_execution arch registers entry entered final_registers acquired after /\
  acquired = entry /\
  uchar_load (event_addr sg eid + OSEventGrp_off) (sem_post_group entry event) after /\
  exists tid old,
    event_task_rdy_entry sg entry.(TskState) eid event tid old /\
    (event_task_rdy_pre sg entry.(TskState) eid event tid old 1 0
       (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
       (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     (critical_region_masked environment.(task_stack_call_platform) critical sg
        call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
      os_sched_context_resources environment.(task_stack_call_external) call **
      sem_post_wake_frame sg entry eid tid **
      armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** retained)) after /\
    (forall priority wake_heap post_cursor post_written post_middle post_final_cursor post_released
      sched_registers sched_final_registers sched_acquired sched_saved_heap
      outgoing old_sp cpsr values lr prefix suffix first old_words publication,
      let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
      let next := os_sched_prefix_state checkpoint in
      let fragments := prefix ++ [(first, first + 16,
        map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
      tid = original.(os_sched_call_stack).(stackLeaseSlot) ->
      os_sched_requests_switch checkpoint = true ->
      hd_error checkpoint.(SchedState).(readyList) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
      os_sched_source_live_save_input sg next outgoing call old_sp cpsr values lr
        prefix suffix first old_words focus publication ->
      (event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
         (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
         (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
       (critical_region_masked environment.(task_stack_call_platform) critical sg
          call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
        os_sched_context_resources environment.(task_stack_call_external) call **
        sem_post_wake_frame sg entry eid tid **
        armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** retained)) wake_heap ->
      post_cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask post_cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore post_cursor wake_heap post_written post_middle ->
      armv7a_restore_suffix_transition restore post_written post_middle post_final_cursor post_released ->
      sched_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr sched_registers.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask sched_registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask final_registers.(kernel_save_r0) ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr sched_registers) checkpoint post_released
        sched_final_registers sched_acquired sched_saved_heap ->
      kernel_call_restore_uninterrupted_execution arch post_cursor wake_heap post_final_cursor post_released /\
      kernel_call_save_uninterrupted_execution arch sched_registers checkpoint post_released
        sched_final_registers sched_acquired sched_saved_heap /\
      sched_acquired = checkpoint /\
      exists prefix_heap current,
        os_sched_source_switch_prefix_execution sg sched_saved_heap prefix_heap /\ current.(statPend) = PendOK /\
        sem_pend_live_switch_stack_return environment critical arch task_abi restore save sg next call old_sp cpsr
          values lr fragments original original_saved eid current perr prefix_heap
          (interrupt_platform_saved environment.(task_stack_call_platform)
             (save_token sched_final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
           critical_region_inside critical sg call.(os_sched_call_invocation) checkpoint ** rest)).

Lemma sem_pend_selected_post_wake_continuation_from_owned :
  forall environment critical sg original suspended incoming selected node state eid waiting
    original_saved original_entry before (outside : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_saved_pointer_at state original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg focus incoming selected node state ** unmap_table_rep sg **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** outside)) before ->
  sem_pend_selected_post_wake_continuation environment critical sg original suspended incoming selected node
    state eid waiting original_saved original_entry before outside.
Proof.
  intros environment critical sg original suspended incoming selected node state eid waiting original_saved
    original_entry before outside abi focus Hactive Hwaiting Hwait Hpointer Hparked Horigin Hbinding Hcall
    Hslice Hmask Howned.
  unfold sem_pend_selected_post_wake_continuation.
  intros arch boundary restore save task_abi previous saved previous_entry event perr rest cursor written
    middle final_cursor released entered registers final_registers acquired after; cbv zeta.
  intros Hselected_call Hprevious_origin Hselected_mask Hlookup Htype Hnonnull Hgroup Hlayout Hframe
    Hr0 Hcursor_mask Hprefix Hsuffix Hboundary Hreturn Hcpsr Hnextmask Hsave.
  eapply sem_pend_selected_post_wake_return_source with (waiting := waiting)
    (previous_entry := previous_entry); try eassumption.
  match type of Howned with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
  { sep_apply_l_atomic Hframe; entailer!. }
  exact (Horder before Howned).
Qed.

(** A proved local continuation of the real wait/Restore source. Its
    arguments are actual finite Save/switch source events and this frame's
    geometry, not a future-safety assumption in a public API Require. *)
Definition sem_pend_wait_sched_switch_continuation
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (call : OsSchedCallContext) (mask : Z)
  (state : UCOS2_Verify_State) (eid : EventID) (node : TaskAbstractState)
  (before : model) (frame : Assertion) : Prop :=
  forall arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  registers final_registers acquired saved_heap
  old_sp cpsr values lr prefix suffix first old_words publication,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state ** frame) in
  state.(SchedState).(readyList) <> [] -> os_sched_requests_switch state = true ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values ->
  armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
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
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists incoming selected installed current,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          let foreign_state := os_sched_install_context call fragments incoming updated in
          os_sched_source_switch_execution environment.(task_stack_call_external) environment.(task_stack_call_platform)
            environment.(task_stack_call_port) abi task_abi sg checkpoint call old_sp cpsr values lr
            suspended incoming selected prefix_heap restored /\
          incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot) /\
          foreign_state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
            Some (task_set_saved_sp node suspended.(armv7a_continuation_sp)) /\
          sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration)
            (task_set_saved_sp node suspended.(armv7a_continuation_sp)) /\
          task_invocation_active foreign_state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
          task_saved_pointer_at foreign_state call.(os_sched_call_stack) suspended.(armv7a_continuation_sp) /\
          foreign_state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
            Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments) /\
          armv7a_task_restored_source environment.(task_stack_call_external) selected /\
          (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
             environment.(task_stack_call_port) abi sg focus incoming selected current foreign_state ** retained) restored /\
          sem_pend_selected_post_wake_continuation environment critical sg call suspended incoming selected current
            foreign_state eid (task_set_saved_sp node suspended.(armv7a_continuation_sp))
            final_registers.(kernel_save_r0) state restored frame)).

Lemma sem_pend_wait_sched_switch_continuation_from_owned :
  forall environment critical sg call mask state eid node before (frame : Assertion),
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration) node ->
  ~ In call.(os_sched_call_stack).(stackLeaseSlot) state.(SchedState).(readyList) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  (os_sched_stack_pre environment kernel_program_inv sg call mask state ** frame) before ->
  sem_pend_wait_sched_switch_continuation environment critical sg call mask state eid node before frame.
Proof.
  intros environment critical sg call mask state eid node before frame Hsource Hnode Hwait Hblocked Habsent Hpre.
  unfold sem_pend_wait_sched_switch_continuation.
  intros arch save task_abi initial registers final_registers acquired saved_heap old_sp cpsr values lr
    prefix suffix first old_words publication
    Hnonempty Hswitch Hreturn Hcpsr Hmask Hfragments Hregion Hbounds Hsprange Hpublication Hlength
    Hcpsr_range Hlr Hranges Htask_mask Hsp_range Hsp Haddress Hsave.
  destruct (sem_pend_wait_sched_switch_source environment critical arch save task_abi initial sg call mask state
    eid node registers before final_registers acquired saved_heap old_sp cpsr values lr prefix suffix first old_words
    publication frame Hsource Hnode Hwait Hblocked Habsent Hnonempty Hswitch Hreturn Hcpsr Hmask Hfragments
    Hregion Hbounds Hsprange Hpublication Hlength Hcpsr_range Hlr Hranges Htask_mask Hsp_range Hsp Haddress
    Hpre Hsave) as [Hsave_run [Hacquired [prefix_heap [written [stored [Hprefix [Hwrites [Hload [Hstore Hselected]]]]]]]]].
  split; [exact Hsave_run|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselected captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [selected [installed [current [Hinstall [Hreads Hrestore]]]]]].
  exists incoming, selected, installed, current; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Hrestored; cbv zeta.
  destruct (Hrestore restored Hrestored) as [Hexecution [Hother [Hlookup [Hcontinuation [Hactive
    [Hpointer [Hparked [Hrestored_source Howned]]]]]]]].
  split; [exact Hexecution|]. split; [exact Hother|]. split; [exact Hlookup|].
  split; [exact Hcontinuation|]. split; [exact Hactive|]. split; [exact Hpointer|].
  split; [exact Hparked|]. split; [exact Hrestored_source|]. split; [exact Howned|].
  eapply sem_pend_selected_post_wake_continuation_from_owned; try eassumption.
  - exact (proj1 Hsource).
  - apply armv7a_task_save_image_binding; exact Hlength.
  - reflexivity.
  - exists (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) prefix **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) suffix).
    cbn [armv7a_task_save_image armv7a_continuation_stack armv7a_continuation_fragments
      armv7a_continuation_words armv7a_continuation_cpsr armv7a_continuation_registers
      armv7a_continuation_lr armv7a_continuation_pc armv7a_continuation_sp].
    rewrite armv7a_task_frame_fragments_split, <- Hsp; entailer!.
  - cbn [armv7a_task_save_image armv7a_continuation_cpsr].
    rewrite armv7a_task_saved_cpsr_mask; exact Htask_mask.
  - match type of Howned with ?P restored => match goal with |- ?Q restored =>
      assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder restored Howned).
Qed.
