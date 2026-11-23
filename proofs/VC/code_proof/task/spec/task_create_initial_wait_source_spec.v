Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.interrupt Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_entry_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The publication state records the fields written by TCBInit.  A later
    normal blocking entry uses these values through this exact lookup;
    neither the CPU execution token nor readiness establishes them. *)
Lemma task_create_published_node_lookup : forall sg publication before node,
  (task_create_stack_publication_state sg publication before).(TskState).(inUsedTaskStates)
    publication.(stack_publication_slot) = Some node ->
  node = task_set_links
    (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image)) before.(TskState).(tcbListHead) None.
Proof.
  intros sg publication before node Hnode.
  change ((task_commit before.(TskState)
    (task_create_stack_publication_args publication).(initPrio)
    publication.(stack_publication_invocation)
    (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image))).(inUsedTaskStates)
        publication.(stack_publication_slot) = Some node) in Hnode.
  unfold task_commit in Hnode; cbn [inUsedTaskStates] in Hnode.
  assert (Hid : (task_tcb_init_commit_node (task_create_stack_publication_args publication)
    publication.(stack_publication_acquired) publication.(stack_publication_slot)
    publication.(stack_publication_image)).(taskID) = publication.(stack_publication_slot)) by reflexivity.
  rewrite Hid in Hnode.
  destruct (Z.eq_dec publication.(stack_publication_slot) publication.(stack_publication_slot));
    [|contradiction].
  inversion Hnode; reflexivity.
Qed.

(** A genuine first-entry frame supplies a usable sixteen-word partition
    and address bounds.  Thus the following continuation has a concrete
    stack split, independently of any proposed future waiting outcome. *)
Lemma task_create_initial_frame_wait_partition : forall selected,
  armv7a_initial_frame_binding selected ->
  exists lower words upper,
    selected.(armv7a_continuation_fragments) =
      task_stack_complete_fragments selected.(armv7a_continuation_stack).(stackLeaseRegion)
        (lower ++ words ++ upper) /\
    selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
      Zlength lower + 16 + Zlength upper /\
    Zlength words = 16 /\
    task_stack_saved_pointer_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_sp) =
      selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionBase) + Zlength lower * sizeof(UINT) /\
    0 <= selected.(armv7a_continuation_sp) < 4294967296.
Proof.
  intros selected [top [entry [argument [task_return [lower [upper [Heq [Hregion [Hsp Hsize]]]]]]]]].
  exists lower, (map (@Some Z) (task_stack_init_frame_words TaskStackNoVFP entry argument task_return 0)), upper.
  split; [rewrite Heq; reflexivity|]. split; [exact Hsize|]. split; [reflexivity|].
  pose proof (Zlength_nonneg lower) as Hlower; pose proof (Zlength_nonneg upper) as Hupper.
  destruct Hregion as [Hwords [Hbase [Halign Hend]]].
  assert (Hrange : selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionBase) <=
    selected.(armv7a_continuation_sp) <
    task_stack_region_end selected.(armv7a_continuation_stack).(stackLeaseRegion)).
  { unfold task_stack_region_end; rewrite Hsp, Hsize, sizeof_uint; lia. }
  split.
  - split; [exact Hrange|]. rewrite Hsp, Z.add_mod, Z.mod_mul by (rewrite sizeof_uint; lia).
    rewrite Halign; reflexivity.
  - split; [exact Hsp|]; lia.
Qed.

Definition task_create_nonempty_stack_fragment (offset : Z) (words : list (option Z))
  : TaskStackFragments :=
  match words with [] => [] | _ => [(offset, offset + Zlength words, words)] end.

Definition task_create_entry_stack_fragments (lower frame upper : list (option Z))
  : TaskStackFragments :=
  task_create_nonempty_stack_fragment 0 lower ++
  [(Zlength lower, Zlength lower + 16, frame)] ++
  task_create_nonempty_stack_fragment (Zlength lower + 16) upper.

Lemma task_create_nonempty_stack_fragment_rep : forall region offset words,
  UIntArray.mixed_full (region.(stackRegionBase) + offset * sizeof(UINT)) (Zlength words) words |--
  task_stack_fragments_rep region (task_create_nonempty_stack_fragment offset words).
Proof.
  intros region offset words; destruct words as [|word rest].
  - unfold task_create_nonempty_stack_fragment, task_stack_fragments_rep, iter_sepcon.
    cbn [map fold_left]; rewrite UIntArray.mixed_full_empty; entailer!.
  - unfold task_create_nonempty_stack_fragment, task_stack_fragments_rep, iter_sepcon.
    cbn [map fold_left task_stack_fragment_rep].
    rewrite UIntArray.mixed_seg_0_shift.
    replace (offset + Zlength (word :: rest) - offset) with (Zlength (word :: rest)) by lia.
    change (UIntArray.mixed_full (region.(stackRegionBase) + offset * sizeof(UINT))
      (Zlength (word :: rest)) (word :: rest) |--
      emp ** UIntArray.mixed_full (region.(stackRegionBase) + offset * sizeof(UINT))
        (Zlength (word :: rest)) (word :: rest)); entailer!.
Qed.

(** The first C-call partition is obtained by ordinary separating-array
    splitting of the restored buffer.  Empty residual pieces own nothing;
    the later context save updates the existing middle sixteen words. *)
Lemma task_create_entry_stack_partition : forall region lower frame upper,
  region.(stackRegionWords) = Zlength lower + 16 + Zlength upper ->
  Zlength frame = 16 ->
  task_stack_fragments_in_range region.(stackRegionWords) 0
    (task_create_entry_stack_fragments lower frame upper) /\
  (task_stack_fragments_rep region (task_stack_complete_fragments region (lower ++ frame ++ upper)) |--
    task_stack_fragments_rep region (task_create_entry_stack_fragments lower frame upper)).
Proof.
  intros region lower frame upper Hsize Hframe.
  pose proof (Zlength_nonneg lower) as Hlower; pose proof (Zlength_nonneg upper) as Hupper.
  split.
  - unfold task_create_entry_stack_fragments, task_create_nonempty_stack_fragment.
    destruct lower as [|l lower], upper as [|u upper];
      cbn [app task_stack_fragments_in_range]; repeat rewrite Zlength_cons in *;
      repeat rewrite Zlength_nil in *;
      try (pose proof (Zlength_nonneg lower)); try (pose proof (Zlength_nonneg upper));
      repeat split; lia.
  - rewrite task_stack_fragments_rep_complete.
    sep_apply_l_atomic (task_stack_storage_split_region region lower frame upper ltac:(lia)).
    unfold task_stack_storage_without_region; rewrite Hframe.
    unfold task_create_entry_stack_fragments; rewrite armv7a_task_frame_fragments_split.
    replace region.(stackRegionBase) with (region.(stackRegionBase) + 0 * sizeof(UINT)) at 2 by lia.
    sep_apply_l_atomic (task_create_nonempty_stack_fragment_rep region 0 lower).
    sep_apply_l_atomic (task_create_nonempty_stack_fragment_rep region (Zlength lower + 16) upper).
    entailer!.
Qed.

(** Initial ARM restore followed by the already approved first-C-entry
    interpretation.  The original pending focus remains unchanged.
    Non-idle follows from the current ready-list order.  The three cleared
    wait fields are supplied by the concrete publication lookup above. *)
Lemma task_create_selected_initial_wait_stage : forall environment
  (initial : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg focus incoming selected node state next tail fragments,
  state.(SchedState).(isRunning) = true ->
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
    selected.(armv7a_continuation_fragments) |--
   task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion) fragments) ->
  state.(SchedState).(readyList) = incoming.(stackLeaseSlot) :: next :: tail ->
  node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [] /\ node.(tcbFlagNode) = 0 ->
  os_sched_source_selected_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg focus incoming selected node state ** unmap_table_rep sg |--
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    fragments in
  let registered := armv7a_initial_call_registered selected state in
  coq_prop (sem_pend_task_call_stage sg call registered /\
    task_stack_live_coverage registered.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call
       (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   kernel_program_inv sg registered **
   armv7a_task_call_stacks environment.(task_stack_call_continuations)
     registered.(TskState) focus registered.(TskState).(parkedTaskStacks)).
Proof.
  intros environment initial sg focus incoming selected node state next tail fragments Hrunning Hinitial
    Hfragments Hpartition Hlist Hfields.
  cbv zeta.
  set (call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    fragments).
  set (registered := armv7a_initial_call_registered selected state).
  unfold os_sched_source_selected_post; Intros.
  assert (Hlease : selected.(armv7a_continuation_stack) = incoming) by tauto.
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node)
    by tauto.
  assert (Hgen : node.(taskGeneration) = incoming.(stackLeaseGeneration)) by tauto.
  assert (Hcovered : task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) by tauto.
  assert (Hcurrent : task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { rewrite Hlease; split; [exact (proj1 (proj2 Hready))|].
    exists node; split; [exact (proj1 Hready)|exact Hgen]. }
  assert (Hobserve : UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) && UCOS2_inv sg state)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hobserve; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  destruct (proj1 (proj1 (proj2 (proj2 Hvalid)))) as [Hmembers [Hsorted Hrest]].
  assert (Hin_next : In next state.(SchedState).(readyList)) by (rewrite Hlist; simpl; tauto).
  destruct (Hmembers next Hin_next) as [other [Hother [Hrange Hother_ready]]].
  rewrite Hlist in Hsorted; cbn [Ucos2Verify.lib.helpers.strictly_sorted_by] in Hsorted.
  rewrite (proj1 Hready), Hother in Hsorted.
  assert (Hnonidle : node.(curPrio) <> sg.(osLowestPrio)) by
    (unfold task_priority_in_range in Hrange; lia).
  unfold armv7a_task_restored_execution; rewrite (armv7a_initial_frame_no_call selected Hinitial).
  sep_apply_l_atomic Hpartition.
  pose proof (armv7a_initial_call_register_resources _ _ _
    environment.(task_stack_call_continuations) initial sg state selected
    fragments Hinitial Hfragments Hcurrent) as Hregister.
  cbv zeta in Hregister; sep_apply_l_atomic Hregister; Intros.
  fold call registered.
  assert (Hsource : kernel_call_task_source call registered) by assumption.
  assert (Hstage : sem_pend_task_call_stage sg call registered).
  { split; [exact Hsource|]. split; [exact Hrunning|]. exists node.
    unfold call, armv7a_initial_call; cbn [os_sched_call_stack].
    rewrite Hlease; split; [exact Hready|]. split; [exact Hgen|]. tauto. }
  assert (Hcoverage : task_stack_live_coverage registered.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { unfold call, armv7a_initial_call; cbn [os_sched_call_stack]; rewrite Hlease; exact Hcovered. }
  rewrite kernel_program_inv_split_unmap.
  change (armv7a_task_call_stacks environment.(task_stack_call_continuations)
    registered.(TskState) focus registered.(TskState).(parkedTaskStacks)) with
    (armv7a_task_call_stacks environment.(task_stack_call_continuations)
      state.(TskState) focus state.(TskState).(parkedTaskStacks)).
  entailer!.
Qed.
(** Preserve the checked initial-frame shape at the actual install/take cut.
    Its resource is consumed by restore once; this pure observation remains
    available to the following C-entry consumer. *)
Lemma task_create_install_selected_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg call outgoing hooked focus (frame : Assertion) heap,
  os_sched_saved_stack_binding call outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key call.(os_sched_call_stack))
     (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi call ** frame)) heap ->
  exists incoming resumed installed selected node,
    os_sched_destination_binding external call outgoing hooked incoming resumed /\
    selected.(armv7a_continuation_fragments) = resumed /\
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
    (forall payload,
      hooked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
      task_stack_key incoming <> armv7a_call_focus_key focus ->
      (os_sched_install_context call outgoing incoming hooked).(TskState).(parkedTaskStacks)
        (armv7a_call_focus_key focus) = Some payload) /\
    (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
      armv7a_task_restored_source external selected /\
      (os_sched_source_selected_post external platform port abi sg focus incoming selected node
         (os_sched_install_context call outgoing incoming hooked) ** frame) restored).
Proof.
  intros external platform port abi task_abi initial sg call outgoing hooked focus frame heap
    Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { match type of Hpre with ?P heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hpre)). }
  destruct (os_sched_covered_high_destination sg call outgoing hooked Hvalid Hsaved Hhigh Hnonempty Hcoverage)
    as [incoming [resumed [node [Hselected [Hnode [Hgeneration [Hpriority [Hlive
      [Hparked [Hin Heffective]]]]]]]]]].
  assert (Hnone : hooked.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None)
    by (unfold os_sched_saved_stack_binding in Hsaved; tauto).
  assert (Hdestination : os_sched_destination_binding external call outgoing hooked incoming resumed).
  { match type of Hpre with ?P heap => assert (Hobserve : P |--
      coq_prop (os_sched_destination_binding external call outgoing hooked incoming resumed) && TT) end.
    { unfold armv7a_task_call_stacks.
      sep_apply_l_atomic (store_parked_continuations_switch (armv7a_task_call_stack_entry abi hooked.(TskState) focus)
        hooked.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) incoming outgoing resumed Hnone Hparked).
      sep_apply_l_atomic (armv7a_task_call_stack_entry_forget external platform port abi hooked.(TskState)
        focus (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed)).
      sep_apply_l_atomic (os_sched_destination_from_stack_entry external platform port abi task_abi initial
        call outgoing hooked incoming resumed node Hselected Hnode Hgeneration Hpriority Hlive Hparked).
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hpre)). }
  destruct (os_sched_install_take_call_continuation external platform port abi sg call outgoing hooked
    incoming resumed focus _ heap Hsaved Hdestination (Haddress _) Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease [Hfragments [Hfocus [Hcurrent [Hcovered Hinstalled]]]]]]]]].
  assert (Hready : sched_current_ready_at (os_sched_install_context call outgoing incoming hooked).(TskState)
    (os_sched_install_context call outgoing incoming hooked).(SchedState) incoming.(stackLeaseSlot) node).
  { unfold sched_current_ready_at.
    change (hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
      hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
      hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true); tauto. }
  assert (Hinitial_frame : selected.(armv7a_continuation_call) = None ->
    armv7a_initial_frame_binding selected).
  { intros Hinitial_call.
    match type of Hinstalled with ?P installed => assert (Hobserve : P |--
      coq_prop (armv7a_initial_frame_binding selected) && TT) end.
    { unfold armv7a_task_continuation_resource; rewrite Hinitial_call.
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve installed Hinstalled)). }
  exists incoming, resumed, installed, selected, node.
  split; [exact Hdestination|]. split; [exact Hfragments|].
  split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hinitial_frame|]. split.
  - intros; eapply os_sched_install_other_keeps_call_lookup; eassumption.
  - intros restored Hrestore.
    match type of Hinstalled with ?P installed => assert (Hinput : P |--
      armv7a_task_switch_control task_abi call **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
      (UCOS2_inv sg (os_sched_install_context call outgoing incoming hooked) **
       armv7a_task_call_stacks abi (os_sched_install_context call outgoing incoming hooked).(TskState)
         focus (os_sched_install_context call outgoing incoming hooked).(TskState).(parkedTaskStacks) ** frame)) end.
    { entailer!. }
    destruct (armv7a_task_restore_resources _ _ _ abi task_abi call selected _ installed restored
      Hreads (Hinput installed Hinstalled) Hrestore) as [Hmemory [Hsource Hrestored]].
    split; [exact Hsource|].
    match type of Hrestored with ?P restored => assert (Hclose : P |--
      os_sched_source_selected_post external platform port abi sg focus incoming selected node
        (os_sched_install_context call outgoing incoming hooked) ** frame) end.
    { unfold os_sched_source_selected_post; entailer!. }
    exact (Hclose restored Hrestored).
Qed.
(** Consume the initial destination installed from the actual publication
    checkpoint.  The former caller's parked payload and SP follow from the
    real park/take and SP-store state, while the new caller's normal waiting
    stage follows from its initialized TCB.  Its next ordinary API entry
    then uses the already proved zero-count wait/return source chain. *)
Lemma task_create_selected_initial_call_wait_return_source : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg source_publication publication_before original original_node suspended incoming resumed selected node
  eid event timeout tail saved original_entry call_before region args task_return lower old_frame upper
  foreign_lower old_words foreign_upper old_sp cpsr values lr (frame : Assertion)
  before entered first_registers first_final acquired after,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let published := task_create_stack_publication_state sg source_publication publication_before in
  let checkpoint := os_sched_prefix_state published in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let state := os_sched_install_context original suspended.(armv7a_continuation_fragments) incoming updated in
  let first := Zlength foreign_lower in
  let prefix := task_create_nonempty_stack_fragment 0 foreign_lower in
  let suffix := task_create_nonempty_stack_fragment (first + 16) foreign_upper in
  let previous := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    (task_create_entry_stack_fragments foreign_lower old_words foreign_upper) in
  let registered := armv7a_initial_call_registered selected state in
  let mask := armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) in
  let call := kernel_sequential_call previous registered.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) registered.(TskState)) registered in
  published.(SchedState).(isRunning) = true ->
  os_sched_requests_switch published = true ->
  published.(SchedState).(readyList) = source_publication.(stack_publication_slot) ::
    original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  os_sched_destination_binding environment.(task_stack_call_external) original
    suspended.(armv7a_continuation_fragments) updated incoming resumed ->
  checkpoint.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some original_node ->
  original_node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  armv7a_initial_frame_binding selected ->
  selected.(armv7a_continuation_fragments) =
    task_stack_complete_fragments selected.(armv7a_continuation_stack).(stackLeaseRegion)
      (foreign_lower ++ old_words ++ foreign_upper) ->
  selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
    first + 16 + Zlength foreign_upper ->
  Zlength old_words = 16 ->
  mutex_query_lookup published eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  0 <= timeout < 4294967296 ->
  task_stack_saved_pointer_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion) (old_sp - 64) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg focus incoming selected node state **
   unmap_table_rep sg **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame)) before ->
  kernel_sequential_call_source boundary previous registered.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered ->
  uchar_load sg.(g_OSIntNesting) 0 entered -> uchar_load sg.(g_OSLockNesting) 0 entered ->
  first_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr first_registers) entry entered
    first_final acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  kernel_call_save_uninterrupted_execution arch first_registers entry entered first_final acquired after /\
  acquired = entry /\
  exists old waited,
    let waiting := event_pend_state sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old PendSem timeout in
    let checkpoint := os_sched_prefix_state waiting in
    let fragments := prefix ++ [(first, first + 16,
      map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
    let foreign_saved := armv7a_task_save_image call old_sp cpsr values lr fragments in
    let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
      foreign_saved.(armv7a_continuation_sp) in
    sem_pend_wait_fragment sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old timeout after waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = first_final.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers sched_acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask first_final.(kernel_save_r0) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers sched_acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers sched_acquired saved_heap /\
        sched_acquired = waiting /\
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
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi call selected installed restored ->
                forall return_cursor return_written return_middle return_final final_heap,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final final_heap ->
                let retained := interrupt_platform_saved environment.(task_stack_call_platform)
                  (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation)
                    call.(os_sched_call_origin)) **
                  critical_region_inside critical sg call.(os_sched_call_invocation) waiting ** frame in
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi
                  sg checkpoint call old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final final_heap /\
                (os_sched_stack_return_post environment kernel_program_inv sg original
                  (armv7a_irq_fiq_mask saved) call_before ** retained) final_heap /\
                (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                  original (armv7a_irq_fiq_mask saved) 0 ** retained) final_heap)))).
Proof.
  intros environment critical arch boundary save restore task_abi initial sg source_publication publication_before
    original original_node suspended incoming resumed selected node eid event timeout tail saved original_entry
    call_before region args task_return lower old_frame upper foreign_lower old_words foreign_upper old_sp cpsr values
    lr frame before entered first_registers first_final acquired after abi focus published checkpoint updated state first
    prefix suffix previous registered mask call entry Hrunning Hswitch Hlist Hdestination Horiginal_node Horiginal_gen
    Horigin Hbinding Hcall Hslice Hsuspended_mask Hactive Hinitial Hinitial_fragments Hsize Hwords Hlookup Hnonnull
    Hlayout Htimeout Hsp_range Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre Hboundary Htype
    Hint Hlock Hfirst_return Hfirst_cpsr Hfirst_mask Hfirst_save Hcount_low Hcount_high.
  pose proof (proj1 (proj1 (os_sched_requests_switch_iff published) Hswitch)) as Henabled.
  assert (Hslot : incoming.(stackLeaseSlot) = source_publication.(stack_publication_slot)).
  { pose proof (proj1 Hdestination) as Hhigh.
    change (checkpoint.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot)) in Hhigh.
    unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint in Hhigh.
    rewrite Henabled, Hswitch in Hhigh; cbn [replace_SchedS SchedState
      sched_increment_switch_counter highRdyTid sched_refresh_high] in Hhigh.
    rewrite Hlist in Hhigh; inversion Hhigh; reflexivity. }
  assert (Hlist_state : state.(SchedState).(readyList) =
    incoming.(stackLeaseSlot) :: original.(os_sched_call_stack).(stackLeaseSlot) :: tail).
  { unfold state, os_sched_install_context; cbn [replace_SchedS SchedState sched_install_selected readyList].
    change (checkpoint.(SchedState).(readyList) = incoming.(stackLeaseSlot) ::
      original.(os_sched_call_stack).(stackLeaseSlot) :: tail).
    unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch.
    cbn [replace_SchedS SchedState sched_increment_switch_counter readyList sched_refresh_high].
    rewrite Hslot; exact Hlist. }
  assert (Hrunning_state : state.(SchedState).(isRunning) = true).
  { unfold state, os_sched_install_context; cbn [replace_SchedS SchedState sched_install_selected isRunning].
    change (checkpoint.(SchedState).(isRunning) = true).
    unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch.
    exact Hrunning. }
  match type of Hpre with ?P before => assert (Hexpose : P |--
    coq_prop (selected.(armv7a_continuation_stack) = incoming /\
      sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node /\
      node.(taskGeneration) = incoming.(stackLeaseGeneration) /\ UCOS2_state_inv sg state) && TT) end.
  { unfold os_sched_source_selected_post, UCOS2_inv; entailer!; try tauto; intros ? ?; exact I. }
  destruct (Hexpose before Hpre) as [[Hlease [Hready [Hgen Hvalid]]] _].
  pose proof (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hvalid))))))) as Hnodup.
  rewrite Hlist_state in Hnodup.
  assert (Hdiffer : incoming.(stackLeaseSlot) <> original.(os_sched_call_stack).(stackLeaseSlot)).
  { inversion Hnodup; intros Heq; subst; apply H1; simpl; auto. }
  assert (Hdifferent : task_stack_key incoming <> armv7a_call_focus_key focus).
  { unfold task_stack_key, armv7a_call_focus_key, focus, armv7a_call_focus.
    cbn [armv7a_focus_call]; intros Heq; apply Hdiffer; inversion Heq; reflexivity. }
  assert (Hpublished_node : published.(TskState).(inUsedTaskStates)
    source_publication.(stack_publication_slot) = Some node).
  { pose proof (proj1 Hready) as Hnode.
    change (updated.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node) in Hnode.
    unfold updated, os_sched_save_current_sp in Hnode; rewrite Horiginal_node in Hnode.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates] in Hnode.
    rewrite (proj2 (Z.eqb_neq _ _) Hdiffer) in Hnode.
    rewrite Hslot in Hnode; exact Hnode. }
  pose proof (task_create_published_node_lookup sg source_publication publication_before node Hpublished_node)
    as Hnode_image.
  assert (Hfields : node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [] /\ node.(tcbFlagNode) = 0).
  { rewrite Hnode_image; repeat split; reflexivity. }
  destruct (task_create_entry_stack_partition selected.(armv7a_continuation_stack).(stackLeaseRegion)
    foreign_lower old_words foreign_upper Hsize Hwords) as [Hgeometry Hpartition].
  rewrite <- Hinitial_fragments in Hpartition.
  pose proof (task_create_selected_initial_wait_stage environment initial sg focus incoming selected node state
    original.(os_sched_call_stack).(stackLeaseSlot) tail
    (task_create_entry_stack_fragments foreign_lower old_words foreign_upper)
    Hrunning_state Hinitial Hgeometry Hpartition Hlist_state Hfields) as Hregister.
  cbv zeta in Hregister; fold abi previous registered in Hregister.
  set (handles := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame).
  match type of Hpre with ?P before => assert (Hregistered : P |--
    coq_prop (sem_pend_task_call_stage sg previous registered /\
      task_stack_live_coverage registered.(TskState) (Some (task_stack_key previous.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
       previous mask ** kernel_program_inv sg registered **
     armv7a_task_call_stacks abi registered.(TskState) focus registered.(TskState).(parkedTaskStacks) ** handles)) end.
  { sepcon_assoc_change; sep_apply_l_atomic Hregister; unfold handles; entailer!. }
  destruct (Hregistered before Hpre) as [[Hstage Hcoverage] Howned].
  assert (Horiginal_lease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hsame; rewrite Hcall in Hsame; symmetry; exact Hsame. }
  assert (Habsent : registered.(TskState).(parkedTaskStacks)
    (task_stack_key previous.(os_sched_call_stack)) = None).
  { change (state.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) = None).
    rewrite Hlease; unfold state, os_sched_install_context.
    cbn [replace_SchedS replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup. }
  assert (Hpending : registered.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { change (state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
      Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
    unfold state, os_sched_install_context.
    cbn [replace_SchedS replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    rewrite task_stack_take_lookup_other by (intro Heq; apply Hdifferent; symmetry; exact Heq).
    apply task_stack_park_fragments_lookup. }
  assert (Hpointer : task_saved_pointer_at registered suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { exists (task_set_saved_sp original_node suspended.(armv7a_continuation_sp)).
    rewrite Horiginal_lease; split; [|split; [exact Horiginal_gen|reflexivity]].
    change (updated.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) =
      Some (task_set_saved_sp original_node suspended.(armv7a_continuation_sp))).
    unfold updated, os_sched_save_current_sp; rewrite Horiginal_node.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hregistered_active : task_invocation_active registered.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { apply task_begin_invocation_preserves_invocation_active; [|exact Hactive].
    pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hregion : valid_task_stack_region previous.(os_sched_call_stack).(stackLeaseRegion)).
  { destruct Hinitial as [top [entry_function [argument [return_address [lo [hi [Heq [Hr Hrest]]]]]]]]; exact Hr. }
  assert (Hpublication : task_publication_happened registered.(TskState)
    source_publication.(stack_publication_invocation) previous.(os_sched_call_stack).(stackLeaseSlot)
      previous.(os_sched_call_stack).(stackLeaseGeneration)).
  { change (task_publication_happened updated.(TskState) source_publication.(stack_publication_invocation)
      selected.(armv7a_continuation_stack).(stackLeaseSlot)
      selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
    rewrite Hlease, Hslot, <- Hgen, Hnode_image.
    unfold updated, os_sched_save_current_sp; rewrite Horiginal_node.
    change (task_publication_happened
      (task_commit publication_before.(TskState) (task_create_stack_publication_args source_publication).(initPrio)
        source_publication.(stack_publication_invocation)
        (task_tcb_init_commit_node (task_create_stack_publication_args source_publication)
          source_publication.(stack_publication_acquired) source_publication.(stack_publication_slot)
          source_publication.(stack_publication_image)))
      source_publication.(stack_publication_invocation) source_publication.(stack_publication_slot)
      source_publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration)).
    apply task_commit_records_history. }
  assert (Hlist_registered : registered.(SchedState).(readyList) =
    previous.(os_sched_call_stack).(stackLeaseSlot) :: original.(os_sched_call_stack).(stackLeaseSlot) :: tail).
  { change (state.(SchedState).(readyList) = selected.(armv7a_continuation_stack).(stackLeaseSlot) ::
      original.(os_sched_call_stack).(stackLeaseSlot) :: tail).
    rewrite Hlease; exact Hlist_state. }
  exact (task_create_foreign_call_wait_return_source environment critical arch boundary save restore task_abi
    sg previous mask registered eid event timeout tail original suspended saved original_entry call_before
    region args task_return lower old_frame upper old_sp cpsr values lr prefix suffix first old_words
    source_publication.(stack_publication_invocation) frame before entered first_registers first_final acquired after
    Hstage Hlist_registered Habsent Hcoverage Horigin Hbinding Hcall Hslice Hsuspended_mask
    Hregistered_active Hpointer Hpending Hlookup Hnonnull Hlayout Htimeout eq_refl Hregion Hgeometry
    Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Howned
    Hboundary Htype Hint Hlock Hfirst_return Hfirst_cpsr Hfirst_mask Hfirst_save Hcount_low Hcount_high).
Qed.
(** A source continuation for the selected initial task.  Arguments describe
    subsequent concrete call/Save/Restore events and the owned stack split.
    The proposition concludes the original public success postcondition; it
    does not assume a future scheduler choice or a future invariant. *)
Definition task_create_initial_wait_continuation environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg source_publication publication_before original suspended incoming selected
  eid event timeout saved call_before region args task_return lower old_frame upper
  (frame : Assertion) before : Prop :=
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let published := task_create_stack_publication_state sg source_publication publication_before in
  let checkpoint := os_sched_prefix_state published in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let state := os_sched_install_context original suspended.(armv7a_continuation_fragments) incoming updated in
  forall foreign_lower old_words foreign_upper old_sp cpsr values lr entered
    first_registers first_final acquired after,
  let first := Zlength foreign_lower in
  let prefix := task_create_nonempty_stack_fragment 0 foreign_lower in
  let suffix := task_create_nonempty_stack_fragment (first + 16) foreign_upper in
  let previous := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    (task_create_entry_stack_fragments foreign_lower old_words foreign_upper) in
  let registered := armv7a_initial_call_registered selected state in
  let mask := armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) in
  let call := kernel_sequential_call previous registered.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) registered.(TskState)) registered in
  selected.(armv7a_continuation_fragments) =
    task_stack_complete_fragments selected.(armv7a_continuation_stack).(stackLeaseRegion)
      (foreign_lower ++ old_words ++ foreign_upper) ->
  selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
    first + 16 + Zlength foreign_upper ->
  Zlength old_words = 16 ->
  task_stack_saved_pointer_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion) (old_sp - 64) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  kernel_sequential_call_source boundary previous registered.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered ->
  uchar_load sg.(g_OSIntNesting) 0 entered -> uchar_load sg.(g_OSLockNesting) 0 entered ->
  first_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr first_registers) entry entered
    first_final acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  kernel_call_save_uninterrupted_execution arch first_registers entry entered first_final acquired after /\
  acquired = entry /\
  exists old waited,
    let waiting := event_pend_state sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old PendSem timeout in
    let checkpoint := os_sched_prefix_state waiting in
    let fragments := prefix ++ [(first, first + 16,
      map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
    let foreign_saved := armv7a_task_save_image call old_sp cpsr values lr fragments in
    let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
      foreign_saved.(armv7a_continuation_sp) in
    sem_pend_wait_fragment sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old timeout after waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = first_final.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers sched_acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask first_final.(kernel_save_r0) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers sched_acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers sched_acquired saved_heap /\
        sched_acquired = waiting /\
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
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi call selected installed restored ->
                forall return_cursor return_written return_middle return_final final_heap,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final final_heap ->
                let retained := interrupt_platform_saved environment.(task_stack_call_platform)
                  (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation)
                    call.(os_sched_call_origin)) **
                  critical_region_inside critical sg call.(os_sched_call_invocation) waiting ** frame in
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi
                  sg checkpoint call old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final final_heap /\
                (os_sched_stack_return_post environment kernel_program_inv sg original
                  (armv7a_irq_fiq_mask saved) call_before ** retained) final_heap /\
                (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                  original (armv7a_irq_fiq_mask saved) 0 ** retained) final_heap)))).
(** The first Scheduler destination and heap are produced here from its
    owned post-save checkpoint.  Initial entry is an observed branch of
    that produced descriptor.  Its checked shape and initialized TCB feed
    the concrete waiting consumer above; no future selected state is an
    input.  The source prefix, stack stores and capture preceding this cut
    are supplied by the existing TaskCreate/Scheduler source producers. *)
Lemma task_create_install_initial_wait_return_source : forall environment critical arch
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
  sg source_publication publication_before original original_node suspended
  eid event timeout tail saved original_entry call_before region args task_return lower old_frame upper
  (frame : Assertion) heap,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let published := task_create_stack_publication_state sg source_publication publication_before in
  let checkpoint := os_sched_prefix_state published in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame) in
  published.(SchedState).(isRunning) = true ->
  os_sched_requests_switch published = true ->
  published.(SchedState).(readyList) = source_publication.(stack_publication_slot) ::
    original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  checkpoint.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some original_node ->
  original_node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active updated.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding original suspended.(armv7a_continuation_fragments) updated ->
  sched_high_ready_consistency updated.(TskState) updated.(SchedState) ->
  task_stack_live_coverage updated.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) ->
  mutex_query_lookup published eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  0 <= timeout < 4294967296 ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (UCOS2_inv sg updated **
   task_stack_fragments_rep original.(os_sched_call_stack).(stackLeaseRegion) suspended.(armv7a_continuation_fragments) **
   armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key original.(os_sched_call_stack))
     (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) **
   armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi original ** retained)) heap ->
  exists incoming resumed installed selected node,
    os_sched_destination_binding environment.(task_stack_call_external) original
      suspended.(armv7a_continuation_fragments) updated incoming resumed /\
    selected.(armv7a_continuation_fragments) = resumed /\
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored, armv7a_task_restore_transition task_abi original selected installed restored ->
      (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
         environment.(task_stack_call_port) abi sg focus incoming selected node
         (os_sched_install_context original suspended.(armv7a_continuation_fragments) incoming updated) **
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
         sg source_publication publication_before original suspended incoming selected
         eid event timeout saved call_before region args task_return lower old_frame upper
         frame restored)).
Proof.
  intros environment critical arch boundary save restore task_abi entry_abi initial sg source_publication
    publication_before original original_node suspended eid event timeout tail saved original_entry call_before
    region args task_return lower old_frame upper frame heap abi focus published checkpoint updated retained
    Hrunning Hswitch Hlist Hnode Hgen Horigin Hbinding Hcall Hslice Hmask Hactive Hsaved Hhigh Hcoverage
    Hlookup Hnonnull Hlayout Htimeout Haddress Hpre.
  pose proof (proj1 (proj1 (os_sched_requests_switch_iff published) Hswitch)) as Henabled.
  assert (Hnonempty : updated.(SchedState).(readyList) <> []).
  { change (checkpoint.(SchedState).(readyList) <> []).
    unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch.
    cbn [replace_SchedS SchedState sched_increment_switch_counter readyList sched_refresh_high].
    rewrite Hlist; discriminate. }
  destruct (task_create_install_selected_source _ _ _ abi task_abi entry_abi sg original
    suspended.(armv7a_continuation_fragments) updated focus retained heap
    Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre)
    as [incoming [resumed [installed [selected [node [Hdestination [Hfragments [Hinstall
      [Hreads [Hinitial Hpending_restore]]]]]]]]]].
  destruct Hpending_restore as [Hpending Hrestore].
  exists incoming, resumed, installed, selected, node.
  split; [exact Hdestination|]. split; [exact Hfragments|]. split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Hactual_restore.
  destruct (Hrestore restored Hactual_restore) as [Hrestored_source Hpost].
  split; [exact Hpost|]. intros Hnone.
  pose proof (Hinitial Hnone) as Hinitial_frame.
  split; [apply task_create_initial_frame_wait_partition; exact Hinitial_frame|].
  unfold task_create_initial_wait_continuation; cbv zeta.
  intros foreign_lower old_words foreign_upper old_sp cpsr values lr entered first_registers first_final
    acquired after Hpartition Hsize Hwords Hsp_range Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp
    Hboundary Htype Hint Hlock Hfirst_return Hfirst_cpsr Hfirst_mask Hfirst_save Hlow Hhigh_count.
  match type of Hpost with ?P restored => assert (Horder : P |--
    os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg focus incoming selected node
      (os_sched_install_context original suspended.(armv7a_continuation_fragments) incoming updated) **
    unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame))
    by (unfold retained; entailer!) end.
  exact (task_create_selected_initial_call_wait_return_source environment critical arch boundary save restore
    task_abi initial sg source_publication publication_before original original_node suspended incoming resumed
    selected node eid event timeout tail saved original_entry call_before region args task_return lower old_frame
    upper foreign_lower old_words foreign_upper old_sp cpsr values lr frame restored entered first_registers
    first_final acquired after Hrunning Hswitch Hlist Hdestination Hnode Hgen Horigin Hbinding Hcall Hslice Hmask
    Hactive Hinitial_frame Hpartition Hsize Hwords Hlookup Hnonnull Hlayout Htimeout Hsp_range Hlength Hcpsr Hlr
    Hranges Hswitch_mask Hsp32 Hsp Haddress (Horder restored Hpost) Hboundary Htype Hint Hlock Hfirst_return
    Hfirst_cpsr Hfirst_mask Hfirst_save Hlow Hhigh_count).
Qed.
