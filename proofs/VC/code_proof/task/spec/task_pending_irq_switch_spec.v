Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSIntCtxSw after its hook: install a different selected task without
    erasing the exact descriptor saved for the interrupted invocation.
    That descriptor is outside the focused map; its physical bytes remain
    in the kernel invariant. The selected entry comes from the remaining
    map and is consumed once. Selection of the retained entry is handled
    by the exact-descriptor return consumer, not by this foreign branch.

    The destination binding is the preceding selector/hook obligation.
    This source-cut theorem is not a public OS_Sched Ensure. *)
Lemma os_int_exit_install_preserves_pending_split : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg transfer retained focus (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) <>
    task_stack_key retained.(armv7a_continuation_stack) ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  task_stack_live_coverage transfer.(os_int_exit_hooked_state).(TskState) None ->
  (UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
   armv7a_dormant_continuation abi retained **
   armv7a_task_call_stacks abi transfer.(os_int_exit_hooked_state).(TskState) focus
     (task_stack_take transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
       retained.(armv7a_continuation_stack)) ** frame) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    selected.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) /\
    (task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    task_current_at (os_int_exit_installed_state transfer)
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
    task_stack_live_coverage (os_int_exit_installed_state transfer).(TskState)
      (Some (task_stack_key transfer.(os_int_exit_incoming_stack))) /\
    (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
      (task_stack_key retained.(armv7a_continuation_stack)) =
      transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
        (task_stack_key retained.(armv7a_continuation_stack)) /\
    (UCOS2_inv sg (os_int_exit_installed_state transfer) **
     armv7a_dormant_continuation abi retained **
     armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
       (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
         retained.(armv7a_continuation_stack)) **
     task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
       selected.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi selected ** frame) installed.
Proof.
  intros external platform port abi sg transfer retained focus frame heap
    Hdestination Hdistinct Haddress Hcoverage Hpre.
  set (state := transfer.(os_int_exit_hooked_state)).
  set (incoming := transfer.(os_int_exit_incoming_stack)).
  set (remaining := task_stack_take state.(TskState).(parkedTaskStacks)
    retained.(armv7a_continuation_stack)).
  pose proof Hdestination as [Hhigh [[node [Hnode [Hgen [Hpriority Hnode_sp]]]]
    [Hlive [Hparked Harch]]]].
  assert (Hlookup : remaining (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), transfer.(os_int_exit_incoming_fragments))).
  { unfold remaining; rewrite task_stack_take_lookup_other by exact Hdistinct; exact Hparked. }
  match type of Hpre with ?P heap =>
    assert (Hextract : P |--
      EX selected,
        coq_prop (armv7a_continuation_binding selected /\
          selected.(armv7a_continuation_stack) = incoming /\
          selected.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) /\
          armv7a_task_frame_slice selected /\
          task_stack_live_sp state.(TskState) (task_stack_key incoming)
            selected.(armv7a_continuation_sp) /\
          (task_stack_key incoming = armv7a_call_focus_key focus ->
            armv7a_continuation_focus_binding focus selected)) &&
        (UCOS2_inv sg state ** armv7a_dormant_continuation abi retained **
         armv7a_task_call_stacks abi state.(TskState) focus (task_stack_take remaining incoming) **
         armv7a_task_continuation_resource abi selected ** frame))
  end.
  { fold state incoming remaining; unfold armv7a_task_call_stacks.
    sep_apply_l_atomic (store_parked_continuations_take
      (armv7a_task_call_stack_entry abi state.(TskState) focus) remaining incoming
      transfer.(os_int_exit_incoming_fragments) Hlookup).
    sep_apply_l_atomic (armv7a_task_call_stack_entry_open external platform port abi state.(TskState)
      focus (task_stack_key incoming) (incoming.(stackLeaseRegion), transfer.(os_int_exit_incoming_fragments))).
    Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
        selected.(armv7a_continuation_fragments)) =
      (incoming.(stackLeaseRegion), transfer.(os_int_exit_incoming_fragments))) by tauto.
    assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey.
      destruct selected.(armv7a_continuation_stack), incoming; cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) =
      transfer.(os_int_exit_incoming_fragments)) by congruence.
    Exists selected; rewrite Hlease, Hfragments; entailer!; tauto. }
  destruct (Hextract heap Hpre) as [selected
    [[Hbinding [Hlease [Hfragments [Hslice [Hsp Hfocus]]]]] Hresources]].
  assert (Hselected_sp : selected.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp)).
  { rewrite <- Hnode_sp; symmetry; apply Hsp; assumption. }
  match type of Hresources with ?P heap =>
    assert (Horder : P |-- UCOS2_inv sg state **
      (armv7a_dormant_continuation abi retained **
       armv7a_task_call_stacks abi state.(TskState) focus (task_stack_take remaining incoming) **
       armv7a_task_continuation_resource abi selected ** frame)) by entailer!
  end.
  destruct (os_int_exit_install_heap_take_destination_frame external sg transfer _ heap
    Hdestination Haddress (Horder heap Hresources))
    as [installed [Hinstall [[Hcurrent Hrestore] Hinstalled]]].
  assert (Hmaps : task_stack_take remaining incoming =
    task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
      retained.(armv7a_continuation_stack)).
  { unfold remaining, incoming, state, os_int_exit_installed_state.
    cbn [replace_TskS replace_SchedS TskState glob_task_set_parked_stacks parkedTaskStacks].
    unfold task_stack_take, field_update; extensionality key.
    repeat destruct task_stack_key_eq_dec; congruence. }
  assert (Hreindex : armv7a_task_call_stacks abi state.(TskState) focus
      (task_stack_take remaining incoming) |--
    armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
      (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
        retained.(armv7a_continuation_stack))).
  { rewrite Hmaps; apply armv7a_task_call_stacks_used_map_eq; reflexivity. }
  match type of Hinstalled with ?P installed =>
    assert (Hclose : P |--
      UCOS2_inv sg (os_int_exit_installed_state transfer) **
      armv7a_dormant_continuation abi retained **
      armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
        (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
          retained.(armv7a_continuation_stack)) **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource abi selected ** frame)
  end.
  { sep_apply_l_atomic Hreindex; rewrite Hlease, Hfragments; entailer!. }
  pose proof (Hclose installed Hinstalled) as Hpost.
  assert (Hreads : armv7a_continuation_restore_reads selected installed).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hpost with ?P installed =>
      assert (Horder_reads : P |--
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) **
        (UCOS2_inv sg (os_int_exit_installed_state transfer) **
         armv7a_dormant_continuation abi retained **
         armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
           (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
             retained.(armv7a_continuation_stack)) **
         armv7a_task_continuation_resource abi selected ** frame)) by entailer!
    end.
    exact (Horder_reads installed Hpost). }
  exists installed, selected.
  split; [rewrite Hselected_sp; exact Hinstall|].
  split; [exact Hreads|]. split; [exact Hlease|]. split; [exact Hfragments|].
  split; [exact Hfocus|]. split; [exact Hcurrent|]. split.
  - apply task_stack_take_covers_selected; exact Hcoverage.
  - split; [|exact Hpost].
    unfold os_int_exit_installed_state.
    cbn [replace_TskS replace_SchedS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup_other; congruence.
Qed.

(** Consume the selected resource at the actual IRQ restore event.
    Initial task entry and resumption of a saved call use their existing
    distinct platform clauses. Neither means that the retained call has
    returned; its exact dormant descriptor stays owned for a later step. *)
Lemma armv7a_irq_switch_restores_selected_call_initial_frame : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg transfer retained focus handler (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) <>
    task_stack_key retained.(armv7a_continuation_stack) ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  task_stack_live_coverage transfer.(os_int_exit_hooked_state).(TskState) None ->
  (UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
   armv7a_dormant_continuation abi retained **
   armv7a_task_call_stacks abi transfer.(os_int_exit_hooked_state).(TskState) focus
     (task_stack_take transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
       retained.(armv7a_continuation_stack)) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    (task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    task_current_at (os_int_exit_installed_state transfer)
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
    task_stack_live_coverage (os_int_exit_installed_state transfer).(TskState)
      (Some (task_stack_key transfer.(os_int_exit_incoming_stack))) /\
    (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
      (task_stack_key retained.(armv7a_continuation_stack)) =
      transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
        (task_stack_key retained.(armv7a_continuation_stack)) /\
    (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
    (forall final, armv7a_restore_transition abi handler selected installed final ->
      final.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      (armv7a_task_restored_execution external platform port abi selected **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg (os_int_exit_installed_state transfer) **
        armv7a_dormant_continuation abi retained **
        armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
          (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
            retained.(armv7a_continuation_stack)) ** frame)) final).
Proof.
  intros external platform port abi initial sg transfer retained focus handler frame heap
    Hdestination Hdistinct Haddress Hcoverage Hpre.
  destruct (os_int_exit_install_preserves_pending_split external platform port abi sg transfer retained
    focus _ heap Hdestination Hdistinct Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease [Hfragments [Hfocus [Hcurrent
      [Hcovered [Hretained Hresources]]]]]]]]]].
  exists installed, selected.
  split; [exact Hinstall|]. split; [exact Hlease|]. split; [exact Hfocus|].
  split; [exact Hcurrent|]. split; [exact Hcovered|]. split; [exact Hretained|].
  split.
  - intro Hnone.
    match type of Hresources with ?P installed =>
      assert (Hobserve : P |-- coq_prop (armv7a_initial_frame_binding selected) && TT) end.
    { unfold armv7a_task_continuation_resource; rewrite Hnone; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve installed Hresources)).
  - intros final Hrun.
  match type of Hresources with ?P installed =>
    assert (Horder : P |--
      interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource abi selected **
      (UCOS2_inv sg (os_int_exit_installed_state transfer) **
       armv7a_dormant_continuation abi retained **
       armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
         (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
           retained.(armv7a_continuation_stack)) ** frame)) by entailer!
  end.
  pose proof (Horder installed Hresources) as Hrestore.
  unfold armv7a_task_restored_execution.
  destruct selected.(armv7a_continuation_call) as [call|] eqn:Hcall.
    + unfold armv7a_task_continuation_resource in Hrestore; rewrite Hcall in Hrestore.
    eapply armv7a_restore_call_resources; eassumption.
    + eapply armv7a_restore_initial_frame; eassumption.
Qed.

(** Compatibility: existing clients keep their complete original conclusion. *)
Lemma armv7a_irq_switch_restores_selected_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg transfer retained focus handler (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) <>
    task_stack_key retained.(armv7a_continuation_stack) ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  task_stack_live_coverage transfer.(os_int_exit_hooked_state).(TskState) None ->
  (UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
   armv7a_dormant_continuation abi retained **
   armv7a_task_call_stacks abi transfer.(os_int_exit_hooked_state).(TskState) focus
     (task_stack_take transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
       retained.(armv7a_continuation_stack)) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    (task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    task_current_at (os_int_exit_installed_state transfer)
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
    task_stack_live_coverage (os_int_exit_installed_state transfer).(TskState)
      (Some (task_stack_key transfer.(os_int_exit_incoming_stack))) /\
    (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
      (task_stack_key retained.(armv7a_continuation_stack)) =
      transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
        (task_stack_key retained.(armv7a_continuation_stack)) /\
    (forall final, armv7a_restore_transition abi handler selected installed final ->
      final.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      (armv7a_task_restored_execution external platform port abi selected **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg (os_int_exit_installed_state transfer) **
        armv7a_dormant_continuation abi retained **
        armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
          (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
            retained.(armv7a_continuation_stack)) ** frame)) final).
Proof.
  intros external platform port abi initial sg transfer retained focus handler frame heap
    Hdestination Hdistinct Haddress Hcoverage Hpre.
  destruct (armv7a_irq_switch_restores_selected_call_initial_frame external platform port abi initial
    sg transfer retained focus handler frame heap Hdestination Hdistinct Haddress Hcoverage Hpre)
    as [installed [selected Hpost]].
  exists installed, selected; tauto.
Qed.

(** The selector/hook cut supplies its actual high-ready cache. Coverage
    and the owned entry below produce the destination binding, including
    its architecture-source observation. The different-key condition is
    this branch of the selected-key comparison, not a public API premise.
    The retained slot may already have been reused with another generation. *)
Lemma armv7a_irq_high_selected_preserves_pending_split_initial_frame : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg state retained focus handler (frame : Assertion) heap,
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  state.(SchedState).(readyList) <> [] ->
  (forall slot node, state.(SchedState).(highRdyTid) = Some slot ->
    state.(TskState).(inUsedTaskStates) slot = Some node ->
    (slot, node.(taskGeneration)) <> task_stack_key retained.(armv7a_continuation_stack)) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_dormant_continuation abi retained **
   armv7a_task_call_stacks abi state.(TskState) focus
     (task_stack_take state.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  exists transfer installed selected node,
    transfer.(os_int_exit_hooked_state) = state /\
    os_int_exit_destination_binding external transfer /\
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    (task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    sched_current_ready_at (os_int_exit_installed_state transfer).(TskState)
      (os_int_exit_installed_state transfer).(SchedState)
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
    task_stack_live_coverage (os_int_exit_installed_state transfer).(TskState)
      (Some (task_stack_key transfer.(os_int_exit_incoming_stack))) /\
    (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
      (task_stack_key retained.(armv7a_continuation_stack)) =
      state.(TskState).(parkedTaskStacks) (task_stack_key retained.(armv7a_continuation_stack)) /\
    (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
    (forall final, armv7a_restore_transition abi handler selected installed final ->
      final.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      (armv7a_task_restored_execution external platform port abi selected **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg (os_int_exit_installed_state transfer) **
        armv7a_dormant_continuation abi retained **
        armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
          (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
            retained.(armv7a_continuation_stack)) ** frame)) final).
Proof.
  intros external platform port abi task_abi initial sg state retained focus handler frame heap
    Hhigh Hnonempty Hdifferent Haddress Hcoverage Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P heap => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hpre)). }
  assert (Hconsistent : parked_stacks_consistent state.(TskState) state.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hready.
  destruct state.(SchedState).(readyList) as [|slot tail] eqn:Hlist; [contradiction|].
  unfold sched_high_ready_consistency in Hhigh; rewrite Hlist in Hhigh.
  destruct Hhigh as [Hhigh [node [Hnode Hpriority]]].
  destruct (Hready slot (or_introl eq_refl)) as [ready_node [Hready_node [Hrange Heffective]]].
  assert (ready_node = node) by congruence; subst ready_node.
  destruct (Hcoverage slot node Hnode) as [Hnone|[region [fragments Hlookup]]]; [discriminate|].
  destruct (Hconsistent slot node.(taskGeneration) region fragments Hlookup)
    as [Hregion [Hgeometry [Hhistory Hlive]]].
  set (incoming := {| stackLeaseRegion := region; stackLeaseSlot := slot;
    stackLeaseGeneration := node.(taskGeneration) |}).
  assert (Hdistinct : task_stack_key incoming <> task_stack_key retained.(armv7a_continuation_stack)).
  { apply (Hdifferent slot node Hhigh Hnode). }
  assert (Hpartial : task_stack_take state.(TskState).(parkedTaskStacks)
      retained.(armv7a_continuation_stack) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments)).
  { rewrite task_stack_take_lookup_other by exact Hdistinct; exact Hlookup. }
  assert (Harch : external.(os_sched_arch_restore_source) incoming node.(tcbStkPtr) fragments).
  { match type of Hpre with ?P heap => assert (Hobserve : P |--
      coq_prop (external.(os_sched_arch_restore_source) incoming node.(tcbStkPtr) fragments) && TT) end.
    { unfold armv7a_task_call_stacks.
      sep_apply_l_atomic (store_parked_continuations_take
        (armv7a_task_call_stack_entry abi state.(TskState) focus)
        (task_stack_take state.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack))
        incoming fragments Hpartial).
      sep_apply_l_atomic (armv7a_task_call_stack_entry_open external platform port abi state.(TskState)
        focus (task_stack_key incoming) (incoming.(stackLeaseRegion), fragments)).
      Intros saved.
      assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
      assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
        saved.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), fragments)) by tauto.
      assert (Hlease : saved.(armv7a_continuation_stack) = incoming).
      { unfold task_stack_key in Hkey; destruct saved.(armv7a_continuation_stack), incoming;
          cbn in *; congruence. }
      assert (Hfragments : saved.(armv7a_continuation_fragments) = fragments) by congruence.
      assert (Hsp : task_stack_live_sp state.(TskState) (task_stack_key incoming)
        saved.(armv7a_continuation_sp)) by tauto.
      assert (Hsaved_sp : node.(tcbStkPtr) = saved.(armv7a_continuation_sp))
        by (apply Hsp; [exact Hnode|reflexivity]).
      sep_apply_l_atomic (armv7a_task_continuation_restore_source external platform port abi task_abi initial saved).
      Intros; entailer!; rewrite Hsaved_sp, <- Hlease, <- Hfragments; assumption. }
    exact (proj1 (Hobserve heap Hpre)). }
  set (transfer := {| os_int_exit_hooked_state := state; os_int_exit_incoming_stack := incoming;
    os_int_exit_incoming_sp := node.(tcbStkPtr); os_int_exit_incoming_fragments := fragments |}).
  assert (Hdestination : os_int_exit_destination_binding external transfer).
  { unfold os_int_exit_destination_binding; cbn [transfer os_int_exit_hooked_state
      os_int_exit_incoming_stack os_int_exit_incoming_sp os_int_exit_incoming_fragments].
    split; [exact Hhigh|]. split.
    - exists node; repeat split; assumption || reflexivity.
    - split.
      + exists node; split; [exact Hnode|]. apply Hlive; [exact Hnode|reflexivity].
      + exact (conj Hlookup Harch). }
  destruct (armv7a_irq_switch_restores_selected_call_initial_frame external platform port abi initial sg transfer
    retained focus handler frame heap Hdestination Hdistinct (Haddress _) Hcoverage Hpre)
    as [installed [selected [Hinstall [Hlease [Hfocus [Hcurrent [Hcovered [Hretained [Hinitial Hrestore]]]]]]]]].
  exists transfer, installed, selected, node.
  split; [reflexivity|]. split; [exact Hdestination|]. split; [exact Hinstall|].
  split; [exact Hlease|]. split; [exact Hfocus|]. split.
  - unfold sched_current_ready_at; change
      (state.(TskState).(inUsedTaskStates) slot = Some node /\
       state.(SchedState).(highRdyTid) = Some slot /\
       state.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
       In slot state.(SchedState).(readyList) /\ is_effectively_ready node.(stat) node.(dly) = true).
    repeat split; try assumption. rewrite Hlist; left; reflexivity.
  - split; [reflexivity|]. exact (conj Hcovered (conj Hretained (conj Hinitial Hrestore))).
Qed.

(** Compatibility: initial-frame provenance is optional for old consumers. *)
Lemma armv7a_irq_high_selected_preserves_pending_split : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg state retained focus handler (frame : Assertion) heap,
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  state.(SchedState).(readyList) <> [] ->
  (forall slot node, state.(SchedState).(highRdyTid) = Some slot ->
    state.(TskState).(inUsedTaskStates) slot = Some node ->
    (slot, node.(taskGeneration)) <> task_stack_key retained.(armv7a_continuation_stack)) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_dormant_continuation abi retained **
   armv7a_task_call_stacks abi state.(TskState) focus
     (task_stack_take state.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  exists transfer installed selected node,
    transfer.(os_int_exit_hooked_state) = state /\
    os_int_exit_destination_binding external transfer /\
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    (task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    sched_current_ready_at (os_int_exit_installed_state transfer).(TskState)
      (os_int_exit_installed_state transfer).(SchedState)
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
    task_stack_live_coverage (os_int_exit_installed_state transfer).(TskState)
      (Some (task_stack_key transfer.(os_int_exit_incoming_stack))) /\
    (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
      (task_stack_key retained.(armv7a_continuation_stack)) =
      state.(TskState).(parkedTaskStacks) (task_stack_key retained.(armv7a_continuation_stack)) /\
    (forall final, armv7a_restore_transition abi handler selected installed final ->
      final.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      (armv7a_task_restored_execution external platform port abi selected **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg (os_int_exit_installed_state transfer) **
        armv7a_dormant_continuation abi retained **
        armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
          (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
            retained.(armv7a_continuation_stack)) ** frame)) final).
Proof.
  intros external platform port abi task_abi initial sg state retained focus handler frame heap
    Hhigh Hnonempty Hdifferent Haddress Hcoverage Hpre.
  destruct (armv7a_irq_high_selected_preserves_pending_split_initial_frame external platform port abi
    task_abi initial sg state retained focus handler frame heap Hhigh Hnonempty Hdifferent Haddress Hcoverage Hpre)
    as [transfer [installed [selected [node Hpost]]]].
  exists transfer, installed, selected, node; tauto.
Qed.


