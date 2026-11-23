Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The outgoing entry is the exact result of this caller's Save/capture.
    Physical installation takes a DIFFERENT selected entry and leaves that
    original descriptor, saved-token and inside owner in the same map. Only
    the parked map and Scheduler caches change during install; used TCBs and
    invocation lifecycle do not, so the resource's TaskState reindex is a
    definitional equality for these actual updates.

    The selected entry retains its existing Some/None interpretation. In
    particular its Some descriptor does not acquire the outgoing call's
    local Save resources or lifecycle registration. *)
Lemma kernel_saved_sched_call_install_foreign_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg call outgoing saved acquired descriptor hooked incoming resumed focus before (frame : Assertion),
  let resource := kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor hooked.(TskState) focus in
  let current := os_sched_install_context call outgoing incoming hooked in
  os_sched_saved_stack_binding call outgoing hooked ->
  os_sched_destination_binding external call outgoing hooked incoming resumed ->
  task_stack_key incoming <> task_stack_key call.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    (task_stack_key incoming = armv7a_call_focus_key focus -> armv7a_continuation_focus_binding focus selected) /\
    task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming)) /\
    current.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
      Some (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) /\
    (forall payload,
      hooked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
      task_stack_key incoming <> armv7a_call_focus_key focus ->
      current.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) /\
    (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
    (forall restored,
      armv7a_task_restore_transition task_abi call selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected ** kernel_program_inv sg current **
       store_parked_continuations
         (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor current.(TskState) focus)
         current.(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi critical task_abi sg call outgoing saved acquired descriptor hooked incoming
    resumed focus before frame resource current Hsaved Hdestination Hother Haddress Hcoverage Hpre.
  destruct (os_sched_install_continuation_map_resources external sg call outgoing hooked incoming resumed resource
    _ before Hsaved Hdestination Haddress Hpre) as [installed [sp [Hrun [[Hcurrent Harch] Hinstalled]]]].
  fold current in Hcurrent, Hinstalled.
  match type of Hinstalled with ?P installed => assert (Hextract : P |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\ armv7a_task_frame_slice selected /\
        task_stack_live_sp hooked.(TskState) (task_stack_key incoming) selected.(armv7a_continuation_sp) /\
        (task_stack_key incoming = armv7a_call_focus_key focus -> armv7a_continuation_focus_binding focus selected)) &&
      (UCOS2_inv sg current **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       store_parked_continuations
         (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor current.(TskState) focus)
         current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) end.
  { unfold resource at 1; unfold kernel_saved_sched_call_entry at 1.
    destruct task_stack_key_eq_dec; [contradiction|].
    sep_apply_l_atomic (armv7a_task_call_stack_entry_open external platform port abi hooked.(TskState)
      focus (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed)); Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
      selected.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct selected.(armv7a_continuation_stack), incoming; cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) = resumed) by congruence.
    change (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor current.(TskState) focus)
      with resource.
    Exists selected; rewrite Hlease, Hfragments; entailer!; tauto. }
  destruct (Hextract installed Hinstalled) as [selected
    [[Hbinding [Hlease [Hfragments [Hslice [Hlive Hfocus]]]]] Howned]].
  pose proof Hdestination as [Hhigh [[node [Hnode [Hgen [Hprio Hsource]]]] Hrest]].
  assert (Hnode_sp : node.(tcbStkPtr) = selected.(armv7a_continuation_sp)) by (apply Hlive; assumption).
  assert (Hload : pointer_load (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) installed).
  { eapply task_stack_framed_live_sp_load with (state := current); [exact Hnode|exact Haddress|].
    match type of Howned with ?P installed => assert (Horder : P |-- UCOS2_inv sg current **
      (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
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
      (UCOS2_inv sg current ** armv7a_task_continuation_resource abi selected **
       store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hcovered : task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) outgoing))
      incoming (task_stack_park_covers_active hooked.(TskState) call.(os_sched_call_stack) outgoing Hcoverage)). }
  assert (Horiginal : current.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), outgoing)).
  { change ((task_stack_take (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
      call.(os_sched_call_stack) outgoing) incoming) (task_stack_key call.(os_sched_call_stack)) =
      Some (call.(os_sched_call_stack).(stackLeaseRegion), outgoing)).
    rewrite task_stack_take_lookup_other by congruence; apply task_stack_park_fragments_lookup. }
  exists installed, selected; split; [exact Hrun|]. split; [exact Hreads|]. split; [exact Hlease|].
  split; [exact Hfragments|]. split; [exact Hfocus|]. split; [exact Hcurrent|]. split; [exact Hcovered|].
  split; [exact Horiginal|]. split.
  - intros; eapply os_sched_install_other_keeps_call_lookup; eassumption.
  - split.
    + intros Hnone.
      match type of Howned with ?P installed => assert (Hinitial : P |--
        coq_prop (armv7a_initial_frame_binding selected) && TT) end.
      { unfold armv7a_task_continuation_resource; rewrite Hnone; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hinitial installed Howned)).
    + intros restored Hrestore.
      match type of Howned with ?P installed => assert (Hrestore_input : P |--
        armv7a_task_switch_control task_abi call **
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
        (kernel_program_inv sg current **
         store_parked_continuations resource current.(TskState).(parkedTaskStacks) ** frame)) end.
      { rewrite kernel_program_inv_split_unmap; entailer!. }
      destruct (armv7a_task_restore_resources _ _ _ abi task_abi call selected _ installed restored
        Hreads (Hrestore_input installed Howned) Hrestore) as [Hmemory [Hrestored_source Hrestored]].
      split; [exact Hmemory|]. split; [exact Hrestored_source|].
      match type of Hrestored with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
      { change (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor current.(TskState) focus)
          with resource; entailer!. }
      exact (Hclose restored Hrestored).
Qed.

(** Actual first foreign installation, starting BEFORE the Scheduler Save.
    The existing producer performs Save, selector, sixteen context writes,
    the outgoing TCB-SP write and capture. The current high-ready cache then
    selects a different task; this is an observed path condition at this
    selector, not a future scheduling or eventual-return promise.

    The exact original entry is retained through the explicit no-write hook
    branch and the physical foreign restore. This endpoint is foreign
    execution, not return of the original OS_Sched or its enclosing API. *)
Lemma kernel_sched_save_foreign_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical arch
  (save : Armv7aSaveSuffixABI external platform critical arch)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg state call node mask focus old_sp cpsr values lr prefix suffix first old_words publication
  registers final_registers acquired before saved_heap (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  os_sched_requests_switch state = true -> state.(SchedState).(readyList) <> [] ->
  checkpoint.(SchedState).(highRdyTid) <> Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus publication ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  kernel_call_task_source call state ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_call_execution_owned external platform call mask ** kernel_program_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call descriptor stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current_node,
        external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
        os_sched_destination_binding external call fragments updated incoming resumed /\
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
        (forall payload,
          updated.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
          task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
        (forall restored,
          armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution external platform port abi task_abi sg checkpoint call old_sp cpsr
            values lr descriptor incoming selected prefix_heap restored /\
          armv7a_task_restored_source external selected /\
          (armv7a_task_restored_execution external platform port abi selected **
           kernel_program_inv sg (os_sched_install_context call fragments incoming updated) **
           store_parked_continuations
             (kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) state descriptor
               (os_sched_install_context call fragments incoming updated).(TskState) focus)
             (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks) ** frame) restored)).
Proof.
  intros external platform port abi critical arch save task_abi initial sg state call node mask focus old_sp cpsr
    values lr prefix suffix first old_words publication registers final_registers acquired before saved_heap frame
    checkpoint fragments descriptor updated Hswitch Hnonempty Hforeign Hinput Hcoverage Hcall_source Hnone
    Hvalid_sr Hmask Hpre Hsave.
  destruct (kernel_sched_save_capture_source external platform port abi critical arch save task_abi sg state call node
    mask focus old_sp cpsr values lr prefix suffix first old_words publication registers final_registers acquired
    before saved_heap frame Hswitch Hnonempty Hinput Hcoverage Hcall_source Hnone Hvalid_sr Hmask Hpre Hsave)
    as [Hsave_run [Hacquired [prefix_heap [written [stored [Hprefix [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]]]]]].
  fold checkpoint fragments descriptor updated in Hstore, Hcovered, Hcapture.
  pose proof Hinput as [Hcurrent [Hnode [Hid [Hgen [Habsent [Hhigh [Hnonempty_checkpoint [Hfocus [Hfragments
    [Hregion [Hgeometry [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges [Hmask192 [Hsp32 [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hhigh_updated : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct checkpoint.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhigh [high [Hlookup Hpriority]]]; split; [exact Hhigh|].
    destruct (Z.eqb head call.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    - apply Z.eqb_eq in Heq; subst head.
      assert (high = node) by congruence; subst high.
      exists (task_set_saved_sp node descriptor.(armv7a_continuation_sp)); split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - exists high; split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup. }
  split; [exact Hsave_run|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hmemory [Hsource Hcaptured_owned]].
  assert (Hvalid : UCOS2_state_inv sg updated).
  { match type of Hcaptured_owned with ?P captured => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg updated) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured_owned)). }
  destruct (os_sched_covered_high_destination sg call fragments updated Hvalid Hsaved Hhigh_updated
    Hnonempty_checkpoint Hcovered) as [incoming [resumed [current_node
      [Hselected [Hselected_node [Hselected_gen [Hpriority [Hlive [Hparked [Hmember Heffective]]]]]]]]]].
  assert (Hother : task_stack_key incoming <> task_stack_key call.(os_sched_call_stack)).
  { intro Heq; apply Hforeign.
    assert (Hslot : incoming.(stackLeaseSlot) = call.(os_sched_call_stack).(stackLeaseSlot))
      by exact (f_equal fst Heq).
    rewrite <- Hslot; exact Hselected. }
  assert (Habsent_updated : updated.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None)
    by (unfold os_sched_saved_stack_binding in Hsaved; tauto).
  assert (Hlookup : updated.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), resumed)).
  { rewrite task_stack_park_fragments_lookup_other in Hparked by exact Hother; exact Hparked. }
  assert (Hdestination : os_sched_destination_binding external call fragments updated incoming resumed).
  { match type of Hcaptured_owned with ?P captured => assert (Hobserve : P |--
      coq_prop (os_sched_destination_binding external call fragments updated incoming resumed) && TT) end.
    { sep_apply_l_atomic (kernel_saved_sched_call_map_without_saved external platform port abi critical sg call
        final_registers.(kernel_save_r0) state descriptor updated.(TskState) focus
        updated.(TskState).(parkedTaskStacks) Habsent_updated).
      unfold armv7a_task_call_stacks.
      sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_call_stack_entry abi updated.(TskState) focus)
        updated.(TskState).(parkedTaskStacks) incoming resumed Hlookup).
      sep_apply_l_atomic (armv7a_task_call_stack_entry_forget external platform port abi updated.(TskState)
        focus (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed)).
      sep_apply_l_atomic (os_sched_destination_from_stack_entry external platform port abi task_abi initial
        call fragments updated incoming resumed current_node Hselected Hselected_node Hselected_gen Hpriority Hlive Hparked).
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured_owned)). }
  destruct (kernel_saved_sched_call_install_foreign_source external platform port abi critical task_abi sg call
    fragments final_registers.(kernel_save_r0) state descriptor updated incoming resumed focus captured frame
    Hsaved Hdestination Hother (Haddress _) Hcovered Hcaptured_owned)
    as [installed [selected [Hinstall [Hreads [Hlease [Hselected_fragments [Hfocused [Hcurrent_selected
      [Hcoverage_selected [Horiginal [Hpending [Hinitial Hrestore]]]]]]]]]]]].
  assert (Hready : sched_current_ready_at (os_sched_install_context call fragments incoming updated).(TskState)
    (os_sched_install_context call fragments incoming updated).(SchedState) incoming.(stackLeaseSlot) current_node).
  { unfold sched_current_ready_at.
    change (updated.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some current_node /\
      updated.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
      updated.(SchedState).(highRdyPrio) = Some current_node.(curPrio) /\
      In incoming.(stackLeaseSlot) updated.(SchedState).(readyList) /\
      is_effectively_ready current_node.(stat) current_node.(dly) = true); tauto. }
  exists incoming, resumed, installed, selected, current_node.
  split; [exact Hsource|]. split; [exact Hdestination|]. split; [exact Hother|].
  split; [exact Hlease|]. split; [exact Hselected_fragments|]. split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Horiginal|]. split; [exact Hready|]. split; [exact Hselected_gen|].
  split; [exact Hcoverage_selected|]. split; [exact Hpending|]. split; [exact Hinitial|].
  intros restored Htask_restore.
  destruct (Hrestore restored Htask_restore) as [Hrestore_memory [Hrestored_source Hrestored]].
  split.
  - exists written, stored, captured, captured, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcaptured
      (conj Hhook_heap (conj Hhook_step (conj Hinstall Htask_restore))))))).
  - exact (conj Hrestored_source Hrestored).
Qed.
