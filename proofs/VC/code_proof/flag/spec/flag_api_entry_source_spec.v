(** Flag API entry observations from existing source producers.
    These are conditional source/ABI composition lemmas. They do not admit
    arbitrary callers, strengthen the port ABI, or verify an application.
    In particular, readiness is retained from an actual selector/publication,
    and clean registration is retained from a concrete initialized TCB. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_irq_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition flag_task_clean_at (tasks : Glob_TaskAbstractState)
  (slot : TaskID) (generation : nat) : Prop :=
  exists node, tasks.(inUsedTaskStates) slot = Some node /\
    node.(taskGeneration) = generation /\ node.(tcbFlagNode) = 0.

(** This observation describes an established entry/return endpoint. It is
    not a universal predicate for KernelCaller and not a future-ready law. *)
Definition flag_api_task_entry_observation (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  kernel_call_task_source call state /\
  flag_task_clean_at state.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) /\
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  state.(SchedState).(readyList) <> [].

Lemma flag_task_publication_clean : forall sg publication before after,
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  flag_task_clean_at after.(TskState) publication.(stack_publication_slot)
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration).
Proof.
  intros sg publication before after [Hinput ->].
  exists (task_set_links
    (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image)) before.(TskState).(tcbListHead) None).
  split.
  - cbn [task_create_stack_publication_state task_create_stack_published_state
      task_tcb_init_published_state task_tcb_init_commit_state task_sched_commit_state
      replace_SchedS replace_TskS TskState glob_task_set_parked_stacks inUsedTaskStates
      task_commit].
    replace (taskID (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image))) with publication.(stack_publication_slot) by reflexivity.
    destruct (Z.eq_dec publication.(stack_publication_slot)
      publication.(stack_publication_slot)); [reflexivity|contradiction].
  - split; reflexivity.
Qed.

Lemma flag_task_save_sp_preserves_clean : forall state slot generation outgoing sp,
  flag_task_clean_at state.(TskState) slot generation ->
  flag_task_clean_at (os_sched_save_current_sp state outgoing sp).(TskState) slot generation.
Proof.
  intros state slot generation outgoing sp [node [Hnode [Hgen Hclean]]].
  unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) outgoing) as [old|] eqn:Hold.
  - destruct (Z.eqb slot outgoing) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst slot.
      rewrite Hnode in Hold; inversion Hold; subst old.
      exists (task_set_saved_sp node sp).
      split; [cbn; rewrite Z.eqb_refl; reflexivity|]. split; assumption.
    + exists node; split; [cbn; rewrite Heq; exact Hnode|]. split; assumption.
  - exists node; split; [exact Hnode|]. split; assumption.
Qed.

Lemma flag_task_prefix_preserves_clean : forall state slot generation,
  flag_task_clean_at state.(TskState) slot generation ->
  flag_task_clean_at (os_sched_prefix_state state).(TskState) slot generation.
Proof. intros; exact H. Qed.

Lemma flag_task_install_preserves_clean : forall state slot generation call fragments incoming,
  flag_task_clean_at state.(TskState) slot generation ->
  flag_task_clean_at (os_sched_install_context call fragments incoming state).(TskState)
    slot generation.
Proof. intros; exact H. Qed.

(** The source publication supplies the zero FlagNode; the precise scheduler
    prefix/SP/install transformations preserve that field, including aliases.
    No intervening arbitrary client or full-lifetime cleanliness is assumed. *)
Lemma flag_published_task_sched_entry_clean : forall sg publication before published
  call sp fragments incoming,
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  let hooked := os_sched_save_current_sp (os_sched_prefix_state published)
    call.(os_sched_call_stack).(stackLeaseSlot) sp in
  flag_task_clean_at (os_sched_install_context call fragments incoming hooked).(TskState)
    publication.(stack_publication_slot)
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration).
Proof.
  intros sg publication before published call sp fragments incoming Hpublication hooked.
  apply flag_task_install_preserves_clean; apply flag_task_save_sp_preserves_clean.
  apply flag_task_prefix_preserves_clean; eapply flag_task_publication_clean; exact Hpublication.
Qed.

Lemma flag_published_task_sched_entry_ready_nonempty : forall sg publication before published
  call sp fragments incoming,
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  (os_sched_install_context call fragments incoming
    (os_sched_save_current_sp (os_sched_prefix_state published)
      call.(os_sched_call_stack).(stackLeaseSlot) sp)).(SchedState).(readyList) <> [].
Proof.
  intros sg publication before published call sp fragments incoming [Hinput ->].
  change ((os_sched_ready_checkpoint (task_create_stack_publication_state sg publication before)).(readyList) <> []).
  rewrite (proj1 (os_sched_ready_checkpoint_frame _)).
  apply task_create_stack_publication_ready_nonempty.
Qed.

(** The original fields installation proof, with the initial-frame fact
    observed from the selected continuation owner before the real restore
    consumes it. All original premises and source/resource conclusions remain. *)

Lemma flag_fields_begin_invocation : forall sg state origin,
  task_invocation_origin_live state.(TskState) origin ->
  UCOS2_fields_inv sg state |--
  UCOS2_fields_inv sg (replace_TskS (task_begin_invocation origin state.(TskState)) state).
Proof.
  intros sg state origin Horigin; unfold UCOS2_fields_inv; Intros.
  pose proof (UCOS2_begin_task_invocation_preserves_validity sg state origin H Horigin) as Hvalid.
  assert (Hraw : UCOS2_fields_raw_rep sg
    (replace_TskS (task_begin_invocation origin state.(TskState)) state) =
    UCOS2_fields_raw_rep sg state).
  { unfold UCOS2_fields_raw_rep; f_equal.
    unfold UCOS2_raw_rep_missing_flag.
    apply UCOS2_raw_rep_missing_module_frame; intros module Hmodule.
    destruct module; try reflexivity.
    - symmetry; apply sched_raw_rep_change_task_index; reflexivity.
    - symmetry; apply event_raw_rep_change_task_index.
      apply event_wait_priority_agreement_encodes.
      unfold event_wait_priority_agreement; intros; reflexivity. }
  rewrite Hraw; entailer!.
Qed.

Lemma flag_fields_selected_continuation_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg call outgoing hooked incoming resumed local before (frame : Assertion),
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context call outgoing incoming hooked in
  os_sched_saved_stack_binding call outgoing hooked ->
  os_sched_destination_binding external call outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming)) /\
    (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
    (forall restored,
      armv7a_task_restore_transition task_abi call selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected ** local selected **
       kernel_program_fields_inv sg current **
       store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
         current.(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi task_abi sg call outgoing hooked incoming resumed local before frame
    resource current Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (os_sched_install_fields_continuation_map_resources external sg call outgoing hooked incoming resumed resource
    _ before Hsaved Hdestination Haddress Hpre) as [installed [sp [Hrun [[Hcurrent Harch] Hinstalled]]]].
  fold current in Hcurrent, Hinstalled.
  match type of Hinstalled with ?P installed => assert (Hextract : P |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\ armv7a_task_frame_slice selected /\
        task_stack_live_sp hooked.(TskState) (task_stack_key incoming) selected.(armv7a_continuation_sp)) &&
      (UCOS2_fields_inv sg current **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       local selected ** store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) end.
  { unfold resource at 1; unfold kernel_saved_continuation_entry at 1; Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
      selected.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct selected.(armv7a_continuation_stack), incoming; cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) = resumed) by congruence.
    Exists selected; rewrite Hlease, Hfragments; entailer!; tauto. }
  destruct (Hextract installed Hinstalled) as
    [selected [[Hbinding [Hlease [Hfragments [Hslice Hlive]]]] Howned]].
  pose proof Hdestination as [Hhigh [[node [Hnode [Hgen [Hprio Hsource]]]] Hrest]].
  assert (Hnode_sp : node.(tcbStkPtr) = selected.(armv7a_continuation_sp)) by (apply Hlive; assumption).
  assert (Hload : pointer_load (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) installed).
  { eapply task_stack_fields_framed_live_sp_load with (state := current); [exact Hnode|exact Haddress|].
    match type of Howned with ?P installed => assert (Horder : P |-- UCOS2_fields_inv sg current **
      (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       local selected ** store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hsp : sp = selected.(armv7a_continuation_sp)).
  { rewrite <- Hnode_sp; eapply pointer_load_deterministic; [exact (proj2 Hrun)|exact Hload]. }
  rewrite Hsp in Hrun.
  assert (Hreads : armv7a_continuation_restore_reads selected installed).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Howned with ?P installed => assert (Horder : P |--
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      (UCOS2_fields_inv sg current ** armv7a_task_continuation_resource abi selected ** local selected **
       store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hcovered : task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) outgoing))
      incoming (task_stack_park_covers_active hooked.(TskState) call.(os_sched_call_stack) outgoing Hcoverage)). }
  exists installed, selected; split; [exact Hrun|]. split; [exact Hreads|]. split; [exact Hbinding|].
  split; [exact Hlease|]. split; [exact Hfragments|]. split; [exact Hcurrent|]. split; [exact Hcovered|].
  split.
  - intro Hnone_selected.
    match type of Howned with ?P installed =>
      assert (Hinitial : P |-- coq_prop (armv7a_initial_frame_binding selected) && TT) end.
    { unfold armv7a_task_continuation_resource; rewrite Hnone_selected;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hinitial installed Howned)).
  - intros restored Hrestore.
  match type of Howned with ?P installed => assert (Hrestore_input : P |--
    armv7a_task_switch_control task_abi call **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
    (local selected ** kernel_program_fields_inv sg current **
     store_parked_continuations resource current.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite kernel_program_fields_inv_split_unmap; entailer!. }
  destruct (armv7a_task_restore_resources _ _ _ abi task_abi call selected _ installed restored
    Hreads (Hrestore_input installed Howned) Hrestore) as [Hmemory [Hresume_source Hrestored]].
  split; [exact Hmemory|]. split; [exact Hresume_source|].
  match type of Hrestored with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
  { change (kernel_saved_continuation_entry abi current.(TskState) local) with resource; entailer!. }
  exact (Hclose restored Hrestored).
Qed.

(** The high-selector observation is kept at the installed endpoint.
    Current readiness here belongs to the actual incoming task only. *)
Lemma flag_selected_task_current_ready : forall external call outgoing hooked incoming resumed node,
  os_sched_destination_binding external call outgoing hooked incoming resumed ->
  hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  sched_current_ready_at (os_sched_install_context call outgoing incoming hooked).(TskState)
    (os_sched_install_context call outgoing incoming hooked).(SchedState)
    incoming.(stackLeaseSlot) node.
Proof.
  intros external call outgoing hooked incoming resumed node
    [Hhigh [[other [Hother [Hgen [Hprio Harch]]]] Hrest]] Hnode Hin Hready.
  rewrite Hnode in Hother; inversion Hother; subst other.
  unfold sched_current_ready_at.
  change (hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
    hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
    hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
    In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
    is_effectively_ready node.(stat) node.(dly) = true).
  tauto.
Qed.

Lemma flag_selected_task_key_taken : forall call outgoing hooked incoming,
  (os_sched_install_context call outgoing incoming hooked).(TskState).(parkedTaskStacks)
    (task_stack_key incoming) = None.
Proof. intros; apply task_stack_take_lookup. Qed.

Lemma flag_fields_sched_selected_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg call outgoing hooked local before (frame : Assertion),
  os_sched_saved_stack_binding call outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   kernel_saved_continuation_entry abi hooked.(TskState) local
     (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations (kernel_saved_continuation_entry abi hooked.(TskState) local)
     hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) before ->
  exists incoming resumed node installed selected,
    let current := os_sched_install_context call outgoing incoming hooked in
    os_sched_destination_binding external call outgoing hooked incoming resumed /\
    sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    sched_current_ready_at current.(TskState) current.(SchedState) incoming.(stackLeaseSlot) node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    current.(TskState).(parkedTaskStacks) (task_stack_key incoming) = None /\
    task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming)) /\
    (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
    (forall restored,
      armv7a_task_restore_transition task_abi call selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected ** local selected **
       kernel_program_fields_inv sg current **
       store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
         current.(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi task_abi initial sg call outgoing hooked local before frame
    Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    UCOS2_fields_inv sg hooked **
    kernel_saved_continuation_entry abi hooked.(TskState) local
      (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations (kernel_saved_continuation_entry abi hooked.(TskState) local)
      hooked.(TskState).(parkedTaskStacks) **
    (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
     armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) by entailer! end.
  destruct (os_sched_fields_continuation_high_destination external platform port abi task_abi initial
    sg call outgoing hooked local _ before Hsaved Hhigh Hnonempty Hcoverage (Horder before Hpre))
    as [incoming [resumed [node [Hdestination [Hnode [Hgen [Hin Hready]]]]]]].
  destruct (flag_fields_selected_continuation_source external platform port abi task_abi
    sg call outgoing hooked incoming resumed local before frame
    Hsaved Hdestination (Haddress _) Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments
      [Hcurrent [Hcovered [Hinitial Hrestore]]]]]]]]]].
  exists incoming, resumed, node, installed, selected; cbv zeta.
  split; [exact Hdestination|]. split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hbinding|]. split; [exact Hlease|]. split; [exact Hfragments|].
  split; [exact Hcurrent|]. split.
  - eapply flag_selected_task_current_ready; eassumption.
  - split; [exact Hgen|]. split; [apply flag_selected_task_key_taken|].
    split; [exact Hcovered|]. split; assumption.
Qed.

Lemma flag_initial_call_fields_resources : forall environment
  (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations)) sg state saved fragments local,
  armv7a_initial_frame_binding saved ->
  task_stack_fragments_in_range
    saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  UCOS2_fields_inv sg state ** armv7a_initial_execution environment.(task_stack_call_continuations) saved **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) fragments **
    os_sched_fields_capsules environment local state |--
  let call := armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  let registered := armv7a_initial_call_registered saved state in
  coq_prop (kernel_call_task_source call registered) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
     UCOS2_fields_inv sg registered ** os_sched_fields_capsules environment local registered).
Proof.
  intros environment entry sg state saved fragments local Hbinding Hfragments Hcurrent.
  cbv zeta.
  destruct (task_current_at_begin_invocation state
    saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) Hcurrent) as [Hcurrent' Hactive].
  sep_apply_l_atomic (flag_fields_begin_invocation sg state
    (RunningInvocation saved.(armv7a_continuation_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_stack).(stackLeaseGeneration)) (proj2 Hcurrent)).
  sep_apply_l_atomic (armv7a_initial_call_resources _ _ _
    environment.(task_stack_call_continuations) entry saved
    state.(TskState).(taskLifecycle).(taskNextInvocation) fragments Hbinding Hfragments).
  unfold kernel_call_task_source, armv7a_initial_call_registered, armv7a_initial_call,
    kernel_call_execution_owned, os_sched_context_resources, os_sched_fields_capsules.
  entailer!.
  exact (proj1 Hcurrent').
Qed.

(** The exact publication-to-selection path supplies clean, global ready
    and taken-key facts together. The task-current fact is the one proved
    by the actual install source above, before registering the first call. *)
Lemma flag_initial_published_entry_observation : forall sg publication before published
  call sp outgoing selected,
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  selected.(armv7a_continuation_stack).(stackLeaseSlot) = publication.(stack_publication_slot) ->
  selected.(armv7a_continuation_stack).(stackLeaseGeneration) =
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) ->
  let current := os_sched_install_context call outgoing selected.(armv7a_continuation_stack)
    (os_sched_save_current_sp (os_sched_prefix_state published)
      call.(os_sched_call_stack).(stackLeaseSlot) sp) in
  task_current_at current selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  flag_api_task_entry_observation
    (armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
      selected.(armv7a_continuation_fragments))
    (armv7a_initial_call_registered selected current).
Proof.
  intros sg publication before published call sp outgoing selected Hpublication Hslot Hgen current Hcurrent.
  destruct (task_current_at_begin_invocation current
    selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) Hcurrent)
    as [Hregistered Hactive].
  unfold flag_api_task_entry_observation.
  split.
  - unfold kernel_call_task_source, armv7a_initial_call.
    split; [reflexivity|]. split; [exact Hactive|exact (proj1 Hregistered)].
  - split.
    + change (flag_task_clean_at current.(TskState)
        selected.(armv7a_continuation_stack).(stackLeaseSlot)
        selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
      rewrite Hslot, Hgen; eapply flag_published_task_sched_entry_clean; exact Hpublication.
    + split.
      * change (current.(TskState).(parkedTaskStacks)
          (task_stack_key selected.(armv7a_continuation_stack)) = None).
        apply flag_selected_task_key_taken.
      * change (current.(SchedState).(readyList) <> []).
        eapply flag_published_task_sched_entry_ready_nonempty; exact Hpublication.
Qed.

Lemma flag_initial_published_entry_resources : forall environment
  (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations)) sg publication before published
  call sp outgoing selected local (frame : Assertion),
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  selected.(armv7a_continuation_stack).(stackLeaseSlot) = publication.(stack_publication_slot) ->
  selected.(armv7a_continuation_stack).(stackLeaseGeneration) =
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) ->
  selected.(armv7a_continuation_call) = None ->
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments) ->
  let current := os_sched_install_context call outgoing selected.(armv7a_continuation_stack)
    (os_sched_save_current_sp (os_sched_prefix_state published)
      call.(os_sched_call_stack).(stackLeaseSlot) sp) in
  task_current_at current selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  let first := armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected current in
  armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected ** local selected **
    kernel_program_fields_inv sg current ** os_sched_fields_capsules environment local current ** frame |--
  coq_prop (flag_api_task_entry_observation first registered) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) first (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
     local selected ** kernel_program_fields_inv sg registered **
     os_sched_fields_capsules environment local registered ** frame).
Proof.
  intros environment entry sg publication before published call sp outgoing selected local frame
    Hpublication Hslot Hgen Hnone Hbinding Hfragments current Hcurrent first registered.
  pose proof (flag_initial_published_entry_observation sg publication before published
    call sp outgoing selected Hpublication Hslot Hgen Hcurrent) as Hentry.
  unfold armv7a_task_restored_execution; rewrite Hnone.
  rewrite !kernel_program_fields_inv_split_unmap.
  sepcon_assoc_change.
  sep_apply_l_atomic (flag_initial_call_fields_resources environment entry sg current selected
    selected.(armv7a_continuation_fragments) local Hbinding Hfragments Hcurrent).
  cbv zeta; unfold first, registered; entailer!; try exact Hentry.
Qed.

Definition flag_sequential_registered_state previous state :=
  replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state.

Lemma flag_sequential_entry_observation : forall previous state,
  flag_api_task_entry_observation previous state ->
  flag_api_task_entry_observation
    (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation))
    (flag_sequential_registered_state previous state).
Proof.
  intros previous state [Hsource [Hclean [Hnone Hready]]].
  pose proof (kernel_call_task_source_current_at previous state Hsource) as Hcurrent.
  destruct Hsource as [Horigin [Hactive Hexecuting]].
  destruct (task_current_at_begin_invocation state previous.(os_sched_call_stack).(stackLeaseSlot)
    previous.(os_sched_call_stack).(stackLeaseGeneration) Hcurrent) as [Hregistered Hfresh].
  unfold flag_api_task_entry_observation, flag_sequential_registered_state, kernel_sequential_call.
  cbn [os_sched_call_origin os_sched_call_invocation os_sched_call_stack].
  rewrite Horigin; split.
  - unfold kernel_call_task_source; cbn.
    split; [reflexivity|]. split; [exact Hfresh|exact (proj1 Hregistered)].
  - split; [exact Hclean|]. split; assumption.
Qed.

(** Transport at the same concrete heap as an actual completed API return
    and next API entry. The ABI produces no ready/clean fact: the preceding
    API return must have established the endpoint observation. *)
Lemma flag_sequential_entry_resources : forall environment
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform)) local sg previous state mask before after (frame : Assertion),
  flag_api_task_entry_observation previous state ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before after ->
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) previous mask **
   kernel_program_fields_inv sg state ** os_sched_fields_capsules environment local state ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := flag_sequential_registered_state previous state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (coq_prop (flag_api_task_entry_observation call registered) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call mask **
     kernel_program_fields_inv sg registered ** os_sched_fields_capsules environment local registered ** frame)) after.
Proof.
  intros environment boundary local sg previous state mask before after frame Hentry Hsource Hpre call registered.
  assert (Horder : kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) previous mask **
    kernel_program_fields_inv sg state ** os_sched_fields_capsules environment local state ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) previous mask **
    (kernel_program_fields_inv sg state ** os_sched_fields_capsules environment local state ** frame)) by entailer!.
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _ Hsource (Horder before Hpre))
    as [Hmemory Hafter].
  split; [exact Hmemory|].
  pose proof (flag_sequential_entry_observation previous state Hentry) as Hnext.
  pose proof (kernel_call_task_source_current_at previous state (proj1 Hentry)) as Hcurrent.
  pose proof (proj1 Hentry) as [Horigin Hactive].
  assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin)).
  { rewrite Horigin; exact (proj2 Hcurrent). }
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { rewrite !kernel_program_fields_inv_split_unmap.
    sep_apply_l_atomic (flag_fields_begin_invocation sg state previous.(os_sched_call_origin) Hlive).
    unfold call, registered, flag_sequential_registered_state, os_sched_fields_capsules; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Only the concrete initialization and allocation domains are covered.
    BootInvocation alone does not imply this property; there is no whole
    pre-start source execution theorem in the registered dependency set. *)
Definition flag_state_has_no_waiters (flags : GlobFlagState) : Prop :=
  (forall id group, flags.(flagUsed) id = Some group -> group.(flagWaitOrder) = []) /\
  (forall pointer, flags.(flagWaitNodes) pointer = None).

Lemma flag_initial_has_no_waiters : forall sg name,
  flag_state_has_no_waiters (flag_initial sg name).
Proof.
  intros; split; [intros id group Hgroup; discriminate|intros; reflexivity].
Qed.

Lemma flag_allocate_preserves_no_waiters : forall flags bits name id after,
  flag_state_has_no_waiters flags ->
  flag_allocate flags bits name = Some (id, after) ->
  flag_state_has_no_waiters after.
Proof.
  intros flags bits name id after [Hgroups Hnodes] Hallocate.
  unfold flag_allocate in Hallocate.
  destruct flags.(flagFree) as [|chosen rest]; [discriminate|].
  destruct (flags.(flagImages) chosen) as [image|]; [|discriminate].
  injection Hallocate as Hid Hafter; subst id after.
  split.
  - intros other group Hgroup; cbn in Hgroup; unfold kernel_map_set in Hgroup.
    destruct (Z.eq_dec other chosen).
    + inversion Hgroup; reflexivity.
    + eapply Hgroups; exact Hgroup.
  - exact Hnodes.
Qed.

(** Preserve actual IRQ descriptor provenance and the exact parked payload. *)
Lemma flag_irq_entry_fields_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler descriptor publication
  (local : Armv7aContinuation -> Assertion) (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice descriptor ->
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
    descriptor.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    descriptor.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre external platform handler **
   (UCOS2_fields_inv sg entry **
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) ** local descriptor ** frame)) before ->
  armv7a_save_transition abi handler descriptor before saved_heap ->
  exists final,
    armv7a_continuation_binding descriptor /\
    descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack) /\
    parked.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
      Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) /\
    descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
    kernel_heap_writes (armv7a_continuation_save_writes descriptor)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) descriptor.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_fields_inv sg parked **
     store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
       parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler descriptor publication local frame before saved_heap
    call parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler descriptor before saved_heap Hsave)
    as [Hactual [Hcall [Hbinding Hrest]]].
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { symmetry; exact Hstack. }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node descriptor.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      descriptor.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hmap : parked.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments))).
  { rewrite Htasks; apply task_stack_park_fragments_lookup. }
  destruct (kernel_irq_save_continuation_fields_resources external platform port abi
    sg entry node handler descriptor publication local frame before saved_heap
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hpre Hsave) as [final Hfinal].
  exists final; split; [exact Hbinding|]. split; [exact Hlease|]. split; assumption.
Qed.


(** Ready-list transport follows the actual source trace at each cut.
    The registered-module premise is the existing sched-ready contract;
    it is not inferred from same-call, safeExec, or a CPU token. *)
Lemma flag_resumption_source_preserves_ready : forall external port critical sg
  observer event_observer origin before stopped returned_origin after,
  kernel_sched_ready_clients critical ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg observer event_observer origin before stopped returned_origin after ->
  UCOS2_state_inv sg before -> before.(SchedState).(readyList) <> [] ->
  after.(SchedState).(readyList) <> [].
Proof.
  intros external port critical sg observer event_observer origin before stopped returned_origin after
    Hclients Hsource Hvalid Hready.
  destruct (kernel_resumption_task_source_trace_erases external port critical.(critical_region_clients)
    sg observer event_observer origin before stopped returned_origin after Hsource) as [Htrace Hactual].
  pose proof (kernel_resumption_resource_trace_transports_invariant kernel_sched_ready_inv
    critical.(critical_region_clients) sg observer event_observer before stopped after
    Hclients Htrace (conj Hvalid Hready)) as Htransport.
  exact (proj2 (proj1 Htransport)).
Qed.

Lemma flag_selected_return_trace_preserves_ready : forall critical sg observer
  installed stopped returned slot node,
  kernel_sched_ready_clients critical ->
  kernel_client_trace critical.(critical_region_clients) sg observer installed stopped returned ->
  UCOS2_state_inv sg installed ->
  sched_current_ready_at installed.(TskState) installed.(SchedState) slot node ->
  returned.(SchedState).(readyList) <> [].
Proof.
  intros critical sg observer installed stopped returned slot node Hclients Htrace Hvalid
    [Hnode [Hcurrent [Hprio [Hin Heffective]]]].
  assert (Hready : installed.(SchedState).(readyList) <> []).
  { intro Hempty; rewrite Hempty in Hin; contradiction. }
  pose proof (kernel_client_trace_transports_invariant kernel_sched_ready_inv
    critical.(critical_region_clients) sg observer installed stopped returned
    Hclients Htrace (conj Hvalid Hready)) as Htransport.
  exact (proj2 (proj1 Htransport)).
Qed.

Lemma flag_irq_park_ready_list_eq : forall state call sp fragments,
  (armv7a_irq_live_parked_state state call sp fragments).(SchedState).(readyList) =
    state.(SchedState).(readyList).
Proof.
  intros; unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    armv7a_irq_entry_counter_state.
  destruct state.(SchedState).(isRunning); reflexivity.
Qed.

Lemma flag_irq_wrapper_take_ready_list_eq : forall state lease,
  (os_int_exit_wrapper_restored_state state lease).(SchedState).(readyList) =
    state.(SchedState).(readyList).
Proof. reflexivity. Qed.

Lemma flag_sched_install_prefix_ready_list_eq : forall state call sp fragments incoming,
  (os_sched_install_context call fragments incoming
    (os_sched_save_current_sp (os_sched_prefix_state state)
      call.(os_sched_call_stack).(stackLeaseSlot) sp)).(SchedState).(readyList) =
    state.(SchedState).(readyList).
Proof.
  intros; change ((os_sched_ready_checkpoint state).(readyList) = state.(SchedState).(readyList)).
  exact (proj1 (os_sched_ready_checkpoint_frame state)).
Qed.

Lemma flag_irq_registry_return_ready : forall external port critical sg observer event_observer
  origin state call sp fragments stopped returned_origin returned,
  kernel_sched_ready_clients critical ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg observer event_observer origin (armv7a_irq_live_parked_state state call sp fragments)
    stopped returned_origin returned ->
  UCOS2_state_inv sg (armv7a_irq_live_parked_state state call sp fragments) ->
  state.(SchedState).(readyList) <> [] ->
  (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(SchedState).(readyList) <> [].
Proof.
  intros external port critical sg observer event_observer origin state call sp fragments
    stopped returned_origin returned Hclients Htrace Hparked Hready.
  rewrite flag_irq_wrapper_take_ready_list_eq.
  eapply flag_resumption_source_preserves_ready; [exact Hclients|exact Htrace|exact Hparked|].
  rewrite flag_irq_park_ready_list_eq; exact Hready.
Qed.


(** The clean/ready observations are produced at the actual protected
    publication heap cut, with the same owners as its existing source rule. *)
Lemma flag_task_publication_entry_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication before,
  UCOS2_state_inv sg before ->
  task_create_stack_publication_input sg publication before ->
  let after := task_create_stack_publication_state sg publication before in
  task_create_stack_publication_resources external platform port abi sg publication before |--
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg before after /\
    flag_task_clean_at after.(TskState) publication.(stack_publication_slot)
      publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) /\
    after.(SchedState).(readyList) <> []) &&
  (UCOS2_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg publication before Hvalid Hinput after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg before after)
    by (split; [exact Hinput|reflexivity]).
  pose proof (flag_task_publication_clean sg publication before after Hstep) as Hclean.
  pose proof (task_create_stack_publication_ready_nonempty sg publication before) as Hready.
  pose proof (task_create_stack_publication_source_post external platform port abi sg publication before
    Hvalid Hinput) as Hpublication.
  cbv zeta in Hpublication.
  sep_apply_l_atomic Hpublication.
  entailer!.
Qed.
