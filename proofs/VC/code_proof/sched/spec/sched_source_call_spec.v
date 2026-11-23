Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Internal SOURCE-CUT interface, not yet a complete OS_Sched C-call
    specification. The entry is OSCtxSw AFTER C selection, not the public
    API's entry before Save. The proved branch has a live outgoing TCB and
    an explicitly supplied no-kernel-write hook execution. Free-current,
    generic hook effects, Boot, IRQ/repeated switching and the surrounding
    Save/C-prefix/Restore paths must be linked before a public callee
    declaration may use a complete source-based contract.

    The strong resource is owned, not an assertion that every endpoint of
    a bare architecture source atom is safe. No old public Require/Ensure
    or ABI field is changed by this file. *)
Definition os_sched_source_switch_pre external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg call focus state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))) &&
  (kernel_call_execution_owned external platform call 192 ** UCOS2_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks)).

(** Only concrete observations, real instructions and the registered
    callback's declared source step occur here. In
    particular validity, readiness, coverage and the returning resource
    assertion are NOT conjuncts of this execution relation. The selected
    descriptor is the one chosen from the owned map by the proof below. *)
Definition os_sched_source_switch_execution external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg state call old_sp cpsr registers lr saved incoming selected before after : Prop :=
  exists written stored captured hooked installed,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    armv7a_task_capture_transition task_abi call saved stored captured /\
    kernel_heap_execution [] captured hooked /\
    kernel_client_step external.(os_sched_hook_action) sg
      (os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp))
      (os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) /\
    sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_task_restore_transition task_abi call selected installed after.

(** This is the selected destination, not necessarily return of the
    original scheduler invocation. Initial task entry and foreign task
    resumption remain distinct in [armv7a_task_restored_execution]. *)
Definition os_sched_source_selected_post external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg focus incoming selected current state : Assertion :=
  coq_prop (selected.(armv7a_continuation_stack) = incoming /\
    (task_stack_key incoming = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) current /\
    current.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) &&
  (armv7a_task_restored_execution external platform port abi selected **
   UCOS2_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks)).

(** Source-stage obligations established by the preceding C/stack owner.
    They concern THIS live TCB and THIS sixteen-word save, not all values
    satisfying an opaque arch_save_source relation. The selected-cache
    fact belongs to the actual C selector cut; it is not global readiness
    of the outgoing task and is not inferred from CPU authority. *)
Definition os_sched_source_live_save_input sg state node call old_sp cpsr registers lr
  prefix suffix first old_words focus publication : Prop :=
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) /\
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  sched_high_ready_consistency state.(TskState) state.(SchedState) /\
  state.(SchedState).(readyList) <> [] /\
  (task_stack_key call.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus call lr lr) /\
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix /\
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) /\
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) /\
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) /\
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) /\
  List.length registers = 13%nat /\
  0 <= cpsr < 4294967296 /\ 0 <= lr < 4294967296 /\
  Forall (fun value => 0 <= value < 4294967296) registers /\
  armv7a_irq_fiq_mask cpsr = 192 /\
  0 <= old_sp - 64 < 4294967296 /\
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) /\
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot).

(** Keep the source facts established inside the selected-entry proof.
    The earlier convenience consumer discarded its destination binding
    and exact fragment equality; that is too weak for a subsequent
    original-call/whole-program source join. This composition reuses the
    actual selector and install/take producers, not a second memory proof.
    In particular the descriptor is linked to THIS map lookup. *)
Lemma os_sched_source_restore_destination_resources_initial_frame : forall external platform port
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
    (forall payload,
      hooked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
      task_stack_key incoming <> armv7a_call_focus_key focus ->
      (os_sched_install_context call outgoing incoming hooked).(TskState).(parkedTaskStacks)
        (armv7a_call_focus_key focus) = Some payload) /\
    (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
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
  exists incoming, resumed, installed, selected, node.
  split; [exact Hdestination|]. split; [exact Hfragments|].
  split; [exact Hinstall|]. split; [exact Hreads|]. split.
  - intros; eapply os_sched_install_other_keeps_call_lookup; eassumption.
  - split.
    + intro Hnone_selected.
      match type of Hinstalled with ?P installed =>
        assert (Hinitial : P |-- coq_prop (armv7a_initial_frame_binding selected) && TT) end.
      { unfold armv7a_task_continuation_resource; rewrite Hnone_selected;
          entailer!; intros ? ?; exact I. }
      exact (proj1 (Hinitial installed Hinstalled)).
    + intros restored Hrestore.
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

(** Compatibility projection; the original interface is unchanged. *)
Lemma os_sched_source_restore_destination_resources : forall external platform port
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
  destruct (os_sched_source_restore_destination_resources_initial_frame external platform port abi
    task_abi initial sg call outgoing hooked focus frame heap Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre)
    as (incoming & resumed & installed & selected & node & Hdestination & Hfragments &
      Hinstall & Hreads & Hpending & Hinitial & Hrestore).
  exists incoming, resumed, installed, selected, node.
  exact (conj Hdestination (conj Hfragments (conj Hinstall (conj Hreads (conj Hpending Hrestore))))).
Qed.

(** The proof produces saved bytes and the selected descriptor from the
    owned world. The later capture/hook/restore arguments are actual
    executions. No premise says that a future restore must occur; nonreturn
    is not silently converted to original-call return. *)
Lemma os_sched_source_live_switch_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (initial : Armv7aInitialEntryABI external platform port abi)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    focus publication (frame : Assertion) before,
  os_sched_source_live_save_input sg state node call old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  (os_sched_source_switch_pre external platform port abi sg call focus state ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming installed selected current,
        external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
        os_sched_saved_stack_binding call fragments updated /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        (forall payload,
          updated.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
          task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution external platform port abi task_abi sg state call old_sp cpsr registers
            lr saved incoming selected before restored /\
          armv7a_task_restored_source external selected /\
          (os_sched_source_selected_post external platform port abi sg focus incoming selected current
             (os_sched_install_context call fragments incoming updated) ** frame) restored)).
Proof.
  intros external platform port abi task_abi initial sg state node call old_sp cpsr registers lr prefix suffix
    first old_words focus publication frame before Hinput Hpre fragments saved updated.
  unfold os_sched_source_live_save_input in Hinput.
  destruct Hinput as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments [Hregion
    [Hgeometry [Hsp_range [Hhistory [Hlength [Hcpsr [Hlr [Hranges [Hmask [Hsp32 [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  assert (Hopen : os_sched_source_switch_pre external platform port abi sg call focus state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned external platform call 192 ** UCOS2_inv sg state **
     armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold os_sched_source_switch_pre; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (task_create_live_switch_selected_source external platform port abi task_abi initial sg state node
    call old_sp cpsr registers lr prefix suffix first old_words focus publication frame before
    Hcurrent Hnode Hid Hgen Hnone Hcoverage Hhigh Hnonempty Hfocus Hfragments Hregion Hgeometry Hsp_range
    Hhistory Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Howned)
    as [written [stored [Hwrites [Hload [Hstore Hsaved]]]]].
  fold fragments saved updated in Hstore, Hsaved.
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hsaved captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [installed [selected [current [Hsource [Hbinding [Hinstall [Hlease [Hfocused
      [Hready [Hgeneration [Hcovered [Hpending Hrestored]]]]]]]]]]]]].
  exists incoming, installed, selected, current.
  split; [exact Hsource|]. split; [exact Hbinding|]. split; [exact Hinstall|]. split; [exact Hpending|].
  intros restored Hrestore.
  destruct (Hrestored restored Hrestore) as [Hmemory [Hrestore_source [Hresources Hsame]]].
  split.
  - exists written, stored, captured, hooked, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcapture
      (conj Hhook_heap (conj Hhook_step (conj Hinstall Hrestore))))))).
  - split; [exact Hrestore_source|].
    match type of Hresources with ?P restored => assert (Hclose : P |--
      os_sched_source_selected_post external platform port abi sg focus incoming selected current
        (os_sched_install_context call fragments incoming updated) ** frame)
    end.
    { unfold os_sched_source_selected_post; entailer!. }
    exact (Hclose restored Hresources).
Qed.

(** Source-rich version of the live save/restore join. The destination
    relation and exact fragments are retained so the C execution can be
    inserted in a whole-program source trace. The unchanged convenience
    theorem above remains available to existing selected-post consumers. *)
Lemma os_sched_source_live_switch_destination_resources_initial_frame :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (initial : Armv7aInitialEntryABI external platform port abi)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    focus publication (frame : Assertion) before,
  os_sched_source_live_save_input sg state node call old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  (os_sched_source_switch_pre external platform port abi sg call focus state ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current,
        external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
        os_sched_destination_binding external call fragments updated incoming resumed /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall payload,
          updated.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
          task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution external platform port abi task_abi sg state call old_sp cpsr
            registers lr saved incoming selected before restored /\
          armv7a_task_restored_source external selected /\
          (os_sched_source_selected_post external platform port abi sg focus incoming selected current
             (os_sched_install_context call fragments incoming updated) ** frame) restored)).
Proof.
  intros external platform port abi task_abi initial sg state node call old_sp cpsr registers lr prefix suffix
    first old_words focus publication frame before Hinput Hpre fragments saved updated.
  unfold os_sched_source_live_save_input in Hinput.
  destruct Hinput as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments [Hregion
    [Hgeometry [Hsp_range [Hhistory [Hlength [Hcpsr [Hlr [Hranges [Hmask [Hsp32 [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  assert (Hopen : os_sched_source_switch_pre external platform port abi sg call focus state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned external platform call 192 ** UCOS2_inv sg state **
     armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)).
  { unfold os_sched_source_switch_pre; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (armv7a_task_save_global_call external platform port abi task_abi sg state node call old_sp
    cpsr registers lr prefix suffix first old_words focus frame before Hcurrent Hnode Hid Hgen Hnone
    Hcoverage Hfocus Hfragments Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp (Haddress _) Howned)
    as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  fold fragments saved updated in Hstore, Hcovered, Hcapture.
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hhigh_after : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhigh [high [Hlookup Hpriority]]]; split; [exact Hhigh|].
    destruct (Z.eqb head call.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    - apply Z.eqb_eq in Heq; subst head.
      assert (high = node) by congruence; subst high.
      exists (task_set_saved_sp node saved.(armv7a_continuation_sp)); split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - exists high; split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hmemory [Hsource Hcaptured_owned]].
  match type of Hcaptured_owned with ?P captured => assert (Horder : P |--
    UCOS2_inv sg updated ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
    armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key call.(os_sched_call_stack))
      (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi call ** frame)) by entailer! end.
  destruct (os_sched_source_restore_destination_resources_initial_frame external platform port abi task_abi initial
    sg call fragments updated focus frame captured Hsaved Hhigh_after Hnonempty Haddress Hcovered
    (Horder captured Hcaptured_owned))
    as [incoming [resumed [installed [selected [current [Hdestination [Hselected_fragments
      [Hinstall [Hreads [Hpending [Hinitial Hrestore_resources]]]]]]]]]]].
  exists incoming, resumed, installed, selected, current.
  split; [exact Hsource|]. split; [exact Hdestination|]. split; [exact Hselected_fragments|].
  split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hpending|].
  split; [exact Hinitial|].
  intros restored Hrestore.
  split.
  - exists written, stored, captured, captured, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcaptured
      (conj Hhook_heap (conj Hhook_step (conj Hinstall Hrestore))))))).
  - exact (Hrestore_resources restored Hrestore).
Qed.

(** Compatibility projection; the original interface is unchanged. *)
Lemma os_sched_source_live_switch_destination_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (initial : Armv7aInitialEntryABI external platform port abi)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    focus publication (frame : Assertion) before,
  os_sched_source_live_save_input sg state node call old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  (os_sched_source_switch_pre external platform port abi sg call focus state ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current,
        external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
        os_sched_destination_binding external call fragments updated incoming resumed /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall payload,
          updated.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
          task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution external platform port abi task_abi sg state call old_sp cpsr
            registers lr saved incoming selected before restored /\
          armv7a_task_restored_source external selected /\
          (os_sched_source_selected_post external platform port abi sg focus incoming selected current
             (os_sched_install_context call fragments incoming updated) ** frame) restored)).
Proof.
  intros external platform port abi task_abi initial sg state node call old_sp cpsr registers lr prefix suffix
    first old_words focus publication frame before Hinput Hpre fragments saved updated.
  destruct (os_sched_source_live_switch_destination_resources_initial_frame external platform port abi
    task_abi initial sg state node call old_sp cpsr registers lr prefix suffix first old_words focus publication
    frame before Hinput Hpre) as [written [stored [Hwrites [Hload [Hstore Hcontinue]]]]].
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hheap Hhook.
  destruct (Hcontinue captured hooked Hcapture Hheap Hhook)
    as (incoming & resumed & installed & selected & current & Hsource & Hdestination & Hfragments &
      Hinstall & Hreads & Hpending & Hinitial & Hrestore).
  exists incoming, resumed, installed, selected, current.
  exact (conj Hsource (conj Hdestination (conj Hfragments
    (conj Hinstall (conj Hreads (conj Hpending Hrestore)))))).
Qed.

(** Actual selected64 OS_Sched C prefix after Save: both nesting reads,
    OS_SchedNew's bitmap/table reads and high-priority write, the priority
    table/high-pointer step, the physical priority-byte comparison, then
    OSCtxSwCtr++. Per-task profiling and TLS are disabled by this profile.
    The guards are observations, not extra implementation tests. *)
Definition os_sched_source_switch_prefix_execution (sg : StableGlobVars)
  (before after : model) : Prop :=
  uchar_load sg.(g_OSIntNesting) 0 before /\
  uchar_load sg.(g_OSLockNesting) 0 before /\
  exists selected high current,
    os_int_exit_selection_heap_fragment sg before selected /\
    uchar_load sg.(g_OSPrioHighRdy) high selected /\
    uchar_load sg.(g_OSPrioCur) current selected /\ high <> current /\
    os_sched_profile_global_fragment sg selected after.

(** The C prefix really PRODUCES the checkpoint needed by the live-switch
    interface. The whole current map, executing call and private frame
    pass only through these masked local C operations. No such frame claim
    is made across a hook or a task switch. *)
Lemma os_sched_source_switch_prefix_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state call focus
  (frame : Assertion) before,
  os_sched_requests_switch state = true -> state.(SchedState).(readyList) <> [] ->
  (os_sched_source_switch_pre external platform port abi sg call focus state **
   unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
      (os_sched_prefix_state state).(SchedState) /\
    (os_sched_source_switch_pre external platform port abi sg call focus
       (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros external platform port abi sg state call focus frame before Hswitch Hnonempty Hpre.
  destruct (proj1 (os_sched_requests_switch_iff state) Hswitch) as [Hselection Hdifferent].
  destruct (proj1 (os_sched_selection_enabled_iff state) Hselection) as [Hints Hlocks].
  assert (Hopen : os_sched_source_switch_pre external platform port abi sg call focus state **
    unmap_table_rep sg ** frame |--
    coq_prop (UCOS2_state_inv sg state /\
      task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (UCOS2_raw_rep sg state ** unmap_table_rep sg **
     (kernel_call_execution_owned external platform call 192 **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold os_sched_source_switch_pre, UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Hraw].
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hguards : uchar_load sg.(g_OSIntNesting) 0 before /\
    uchar_load sg.(g_OSLockNesting) 0 before).
  { match type of Hraw with ?P before => assert (Hi : P |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT)
    end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; rewrite Hints; entailer!; intros ? ?; exact I. }
    match type of Hraw with ?P before => assert (Hl : P |-- sg.(g_OSLockNesting) # UChar |-> 0 ** TT)
    end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; rewrite Hlocks; entailer!; intros ? ?; exact I. }
    split; eapply framed_uchar_store_load; [exact (Hi before Hraw)|exact (Hl before Hraw)]. }
  destruct (os_int_exit_selection_raw_frame_post sg state _ before Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hnonempty Hraw)
    as [selected [Hselect [Hhighread [Hcurrentread Hselected]]]].
  destruct Hselected as [selected_owned [rest [Hjoin
    [[raw [unmap [Hselected_join [Hselected_raw Hunmap]]]] Hrest]]]].
  destruct (os_sched_profile_global_raw_post sg (os_int_exit_selection_state state) raw Hselected_raw)
    as [counted [Hcounter Hcounted]].
  destruct (os_sched_profile_global_fragment_frame sg raw counted unmap selected_owned
    Hcounter Hselected_join) as [counted_owned [Hcounter_owned Hcounted_join]].
  destruct (os_sched_profile_global_fragment_frame sg selected_owned counted_owned rest selected
    Hcounter_owned Hjoin) as [after [Hcounter_whole Hafter_join]].
  assert (Hstate : os_sched_profile_global_state (os_int_exit_selection_state state) = os_sched_prefix_state state).
  { unfold os_sched_profile_global_state, os_int_exit_selection_state, os_sched_prefix_state,
      os_sched_ready_checkpoint; rewrite Hselection, Hswitch; reflexivity. }
  assert (Hvalid_after : UCOS2_state_inv sg (os_sched_prefix_state state)).
  { apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid. }
  assert (Hafter : (UCOS2_raw_rep sg (os_sched_prefix_state state) ** unmap_table_rep sg **
    (kernel_call_execution_owned external platform call 192 **
     armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)) after).
  { exists counted_owned, rest; split; [exact Hafter_join|]. split; [|exact Hrest].
    exists counted, unmap; split; [exact Hcounted_join|]. split; [rewrite <- Hstate; exact Hcounted|exact Hunmap]. }
  exists after; split.
  - split; [exact (proj1 Hguards)|]. split; [exact (proj2 Hguards)|].
    exists selected, (sched_selected_priority state.(TskState) state.(SchedState)),
      (sched_priority_byte state.(SchedState).(curSchedPrio)).
    exact (conj Hselect (conj Hhighread (conj Hcurrentread (conj Hdifferent Hcounter_whole)))).
  - split.
    + apply os_sched_ready_checkpoint_high_consistency with (sg := sg);
        [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hselection].
    + match type of Hafter with ?P after => assert (Hclose : P |--
        os_sched_source_switch_pre external platform port abi sg call focus (os_sched_prefix_state state) **
        unmap_table_rep sg ** frame)
      end.
      { unfold os_sched_source_switch_pre, UCOS2_inv;
          change (os_sched_prefix_state state).(TskState) with state.(TskState); entailer!. }
      exact (Hclose after Hafter).
Qed.

(** Recover the pending invocation only when the ACTUAL chosen lease is
    its focus. This keeps the derived ready fact and CURRENT whole map.
    It does not claim this is already the OS_Sched C return: the matching
    Restore and later source continuation must still consume this owner. *)
Lemma os_sched_source_selected_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus incoming selected current state,
  task_stack_key incoming = armv7a_call_focus_key focus ->
  os_sched_source_selected_post external platform port abi sg focus incoming selected current state |--
  coq_prop (sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) current /\
    current.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) &&
  (kernel_call_execution_owned external platform
     (armv7a_continuation_resumed_call selected focus.(armv7a_focus_call))
     (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   UCOS2_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg focus incoming selected current state Hkey.
  unfold os_sched_source_selected_post; Intros.
  assert (Hfocused : armv7a_continuation_focus_binding focus selected) by tauto.
  assert (Hcall : selected.(armv7a_continuation_call) = Some focus.(armv7a_focus_call)).
  { unfold armv7a_continuation_focus_binding in Hfocused; tauto. }
  unfold armv7a_task_restored_execution; rewrite Hcall; entailer!.
Qed.
