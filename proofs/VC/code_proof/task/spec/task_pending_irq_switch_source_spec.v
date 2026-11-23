Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected single-event/non-profiling source configuration. The C
    operations after the nesting decrement are source-identical to the
    scheduler prefix; this reuse does NOT model a call to OS_Sched.
    No ready/invariant test or postcondition is inserted in the execution. *)
Definition os_int_exit_source_switch_prefix_execution (sg : StableGlobVars)
  (before after : model) : Prop :=
  exists counted,
    os_int_exit_masked_counter_fragment sg before true counted /\
    os_sched_source_switch_prefix_execution sg counted after.

Lemma os_int_exit_source_switch_prefix_frame_post : forall sg state
  (frame : Assertion) before,
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  (UCOS2_inv sg state ** unmap_table_rep sg ** frame) before ->
  exists after,
    os_int_exit_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_int_exit_ready_checkpoint true state).(TskState)
      (os_int_exit_ready_checkpoint true state).(SchedState) /\
    (UCOS2_inv sg (os_int_exit_ready_checkpoint true state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before Hrunning Hswitch Hnonempty Hpre.
  assert (Hopen : UCOS2_inv sg state ** unmap_table_rep sg ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (UCOS2_raw_rep sg state ** (unmap_table_rep sg ** frame))).
  { unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [Hvalid [owned [rest [Hjoin [Hraw Hframe]]]]].
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw)
    as [counter_owned [Hcounter Hcounter_raw]].
  rewrite Hrunning in Hcounter, Hcounter_raw.
  destruct (os_int_exit_masked_counter_fragment_frame sg owned true counter_owned rest before Hcounter Hjoin)
    as [counted [Hcount Hcount_join]].
  assert (Hcounted : (UCOS2_raw_rep sg (os_int_exit_counter_state true state) **
    unmap_table_rep sg ** frame) counted).
  { assert (Horder : UCOS2_raw_rep sg (os_int_exit_counter_state true state) **
      (unmap_table_rep sg ** frame) |-- UCOS2_raw_rep sg (os_int_exit_counter_state true state) **
      unmap_table_rep sg ** frame) by entailer!.
    apply Horder; exists counter_owned, rest; split; [exact Hcount_join|]; split; assumption. }
  assert (Hswitch_counted : os_sched_requests_switch (os_int_exit_counter_state true state) = true)
    by exact Hswitch.
  destruct (proj1 (os_sched_requests_switch_iff _) Hswitch_counted) as [Hselection Hdifferent].
  destruct (proj1 (os_sched_selection_enabled_iff _) Hselection) as [Hints Hlocks].
  assert (Hguards : uchar_load sg.(g_OSIntNesting) 0 counted /\
    uchar_load sg.(g_OSLockNesting) 0 counted).
  { match type of Hcounted with ?P counted =>
      assert (Hi : P |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT) end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; rewrite Hints; entailer!;
        intros ? ?; exact I. }
    match type of Hcounted with ?P counted =>
      assert (Hl : P |-- sg.(g_OSLockNesting) # UChar |-> 0 ** TT) end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; rewrite Hlocks; entailer!;
        intros ? ?; exact I. }
    split; eapply framed_uchar_store_load; [exact (Hi counted Hcounted)|exact (Hl counted Hcounted)]. }
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  destruct (os_int_exit_selection_raw_frame_post sg (os_int_exit_counter_state true state) frame counted Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hnonempty Hcounted)
    as [selected [Hselect [Hhighread [Hcurrentread Hselected]]]].
  destruct Hselected as [selected_owned [rest_selected [Hselected_join
    [[raw [unmap [Hraw_join [Hselected_raw Hunmap]]]] Hrest]]]].
  destruct (os_sched_profile_global_raw_post sg
    (os_int_exit_selection_state (os_int_exit_counter_state true state)) raw Hselected_raw)
    as [counted_owned [Hcounter_update Hcounted_raw]].
  destruct (os_sched_profile_global_fragment_frame sg raw counted_owned unmap selected_owned
    Hcounter_update Hraw_join) as [counted_shared [Hcounter_shared Hshared_join]].
  destruct (os_sched_profile_global_fragment_frame sg selected_owned counted_shared rest_selected selected
    Hcounter_shared Hselected_join) as [after [Hcounter_whole Hafter_join]].
  assert (Hstate : os_sched_profile_global_state
      (os_int_exit_selection_state (os_int_exit_counter_state true state)) =
    os_int_exit_ready_checkpoint true state).
  { change (os_sched_profile_global_state (os_int_exit_selection_state (os_int_exit_counter_state true state)) =
      os_sched_prefix_state (os_int_exit_counter_state true state)).
    unfold os_sched_profile_global_state, os_int_exit_selection_state, os_sched_prefix_state,
      os_sched_ready_checkpoint; rewrite Hselection, Hswitch_counted; reflexivity. }
  assert (Hvalid_after : UCOS2_state_inv sg (os_int_exit_ready_checkpoint true state))
    by (apply os_int_exit_ready_checkpoint_preserves_validity; exact Hvalid).
  assert (Hafter : (UCOS2_raw_rep sg (os_int_exit_ready_checkpoint true state) **
    unmap_table_rep sg ** frame) after).
  { exists counted_shared, rest_selected; split; [exact Hafter_join|]. split; [|exact Hrest].
    exists counted_owned, unmap; split; [exact Hshared_join|]. split.
    - rewrite <- Hstate; exact Hcounted_raw.
    - exact Hunmap. }
  exists after; split.
  - exists counted; split; [exact Hcount|].
    split; [exact (proj1 Hguards)|]. split; [exact (proj2 Hguards)|].
    exists selected, (sched_selected_priority state.(TskState) state.(SchedState)),
      (sched_priority_byte state.(SchedState).(curSchedPrio)).
    exact (conj Hselect (conj Hhighread (conj Hcurrentread (conj Hdifferent Hcounter_whole)))).
  - split.
    + apply os_sched_ready_checkpoint_high_consistency with (sg := sg).
      * exact (proj1 (proj1 (proj2 (proj2 Hvalid)))).
      * exact Hselection.
    + match type of Hafter with ?P after => assert (Hclose : P |--
        UCOS2_inv sg (os_int_exit_ready_checkpoint true state) ** unmap_table_rep sg ** frame) end.
      { unfold UCOS2_inv; entailer!. }
      exact (Hclose after Hafter).
Qed.

(** This hook branch is explicit: the registered hook has a no-write
    execution and its source action preserves the checkpoint. A different
    hook needs its own checked resource producer. No task-level frame save
    is inserted in OSIntCtxSw: IRQ entry already deposited that frame. *)
Definition os_int_exit_source_selected_execution external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg state handler transfer selected (before after : model) : Prop :=
  exists prepared hooked installed,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    kernel_heap_execution [] prepared hooked /\
    kernel_client_step external.(os_sched_hook_action) sg
      (os_int_exit_ready_checkpoint true state) transfer.(os_int_exit_hooked_state) /\
    sched_install_heap_fragment sg hooked installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_restore_transition abi handler selected installed after.

Lemma armv7a_irq_switch_source_preserves_pending_split_initial_frame : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg state retained focus handler (frame : Assertion) before,
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  (forall slot node, (os_int_exit_ready_checkpoint true state).(SchedState).(highRdyTid) = Some slot ->
    state.(TskState).(inUsedTaskStates) slot = Some node ->
    (slot, node.(taskGeneration)) <> task_stack_key retained.(armv7a_continuation_stack)) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage state.(TskState) None ->
  kernel_client_step external.(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true state) (os_int_exit_ready_checkpoint true state) ->
  (UCOS2_inv sg state ** unmap_table_rep sg **
   (armv7a_dormant_continuation abi retained **
    armv7a_task_call_stacks abi state.(TskState) focus
      (task_stack_take state.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame))) before ->
  exists prepared,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    (forall hooked, kernel_heap_execution [] prepared hooked ->
      exists transfer installed selected node,
        transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true state /\
        os_int_exit_destination_binding external transfer /\
        sched_install_heap_fragment sg hooked installed
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
          os_int_exit_source_selected_execution external platform port abi
            sg state handler transfer selected before final /\
          (armv7a_task_restored_execution external platform port abi selected **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           (UCOS2_inv sg (os_int_exit_installed_state transfer) **
            armv7a_dormant_continuation abi retained **
            armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
              (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
                retained.(armv7a_continuation_stack)) ** (unmap_table_rep sg ** frame))) final)).
Proof.
  intros external platform port abi task_abi initial sg state retained focus handler frame before
    Hrunning Hswitch Hnonempty Hdifferent Haddress Hcoverage Hhook Hpre.
  destruct (os_int_exit_source_switch_prefix_frame_post sg state _ before
    Hrunning Hswitch Hnonempty Hpre) as [prepared [Hprefix [Hhigh Hprepared]]].
  exists prepared; split; [exact Hprefix|].
  intros hooked Hhook_run.
  assert (Hsame : hooked = prepared).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_run|].
    split; [constructor|auto]. }
  subst hooked.
  match type of Hprepared with ?P prepared =>
    assert (Horder : P |--
      UCOS2_inv sg (os_int_exit_ready_checkpoint true state) **
      armv7a_dormant_continuation abi retained **
      armv7a_task_call_stacks abi (os_int_exit_ready_checkpoint true state).(TskState) focus
        (task_stack_take (os_int_exit_ready_checkpoint true state).(TskState).(parkedTaskStacks)
          retained.(armv7a_continuation_stack)) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (unmap_table_rep sg ** frame))) by entailer!
  end.
  assert (Hcheckpoint_nonempty :
    (os_int_exit_ready_checkpoint true state).(SchedState).(readyList) <> []).
  { change ((os_sched_ready_checkpoint (os_int_exit_after_nesting state)).(readyList) <> []).
    unfold os_sched_ready_checkpoint.
    destruct (os_sched_selection_enabled (os_int_exit_after_nesting state));
      [destruct (os_sched_requests_switch (os_int_exit_after_nesting state))|]; exact Hnonempty. }
  destruct (armv7a_irq_high_selected_preserves_pending_split_initial_frame external platform port abi task_abi initial
    sg (os_int_exit_ready_checkpoint true state) retained focus handler (unmap_table_rep sg ** frame)
    prepared Hhigh Hcheckpoint_nonempty Hdifferent Haddress Hcoverage (Horder prepared Hprepared))
    as [transfer [installed [selected [node [Hstate [Hdestination [Hinstall [Hlease [Hfocus
      [Hready [Hgeneration [Hcovered [Hretained [Hinitial Hrestore]]]]]]]]]]]]]].
  exists transfer, installed, selected, node.
  split; [exact Hstate|]. split; [exact Hdestination|]. split; [exact Hinstall|].
  split; [exact Hlease|]. split; [exact Hfocus|]. split; [exact Hready|].
  split; [exact Hgeneration|]. split; [exact Hcovered|]. split; [exact Hretained|]. split; [exact Hinitial|].
  intros final Hrun; split.
  - exists prepared, prepared, installed.
    split; [exact Hprefix|]. split; [exact Hhook_run|].
    split; [rewrite Hstate; exact Hhook|]. exact (conj Hinstall Hrun).
  - exact (proj2 (Hrestore final Hrun)).
Qed.

(** Existing callers retain their original source and resource result. *)
Lemma armv7a_irq_switch_source_preserves_pending_split : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg state retained focus handler (frame : Assertion) before,
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  (forall slot node, (os_int_exit_ready_checkpoint true state).(SchedState).(highRdyTid) = Some slot ->
    state.(TskState).(inUsedTaskStates) slot = Some node ->
    (slot, node.(taskGeneration)) <> task_stack_key retained.(armv7a_continuation_stack)) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage state.(TskState) None ->
  kernel_client_step external.(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true state) (os_int_exit_ready_checkpoint true state) ->
  (UCOS2_inv sg state ** unmap_table_rep sg **
   (armv7a_dormant_continuation abi retained **
    armv7a_task_call_stacks abi state.(TskState) focus
      (task_stack_take state.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame))) before ->
  exists prepared,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    (forall hooked, kernel_heap_execution [] prepared hooked ->
      exists transfer installed selected node,
        transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true state /\
        os_int_exit_destination_binding external transfer /\
        sched_install_heap_fragment sg hooked installed
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
          os_int_exit_source_selected_execution external platform port abi
            sg state handler transfer selected before final /\
          (armv7a_task_restored_execution external platform port abi selected **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           (UCOS2_inv sg (os_int_exit_installed_state transfer) **
            armv7a_dormant_continuation abi retained **
            armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
              (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
                retained.(armv7a_continuation_stack)) ** (unmap_table_rep sg ** frame))) final)).
Proof.
  intros external platform port abi task_abi initial sg state retained focus handler frame before
    Hrunning Hswitch Hnonempty Hdifferent Haddress Hcoverage Hhook Hpre.
  destruct (armv7a_irq_switch_source_preserves_pending_split_initial_frame external platform port abi
    task_abi initial sg state retained focus handler frame before Hrunning Hswitch Hnonempty Hdifferent
    Haddress Hcoverage Hhook Hpre) as [prepared [Hprefix Hcontinue]].
  exists prepared; split; [exact Hprefix|].
  intros hooked Hrun; destruct (Hcontinue hooked Hrun) as [transfer [installed [selected [node Hpost]]]].
  exists transfer, installed, selected, node; tauto.
Qed.


