Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_recheck_reuse_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_call_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_recycle_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** During another task's actual execution the live coverage has a Some
    key. The earlier interrupted call remains in this same focused map.
    This is a view of existing resources, with no additional OS field. *)
Definition mutex_del_focused_world {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg focus payload active state : Assertion :=
  coq_prop (mutex_program_selected_reachable sg state /\
    mutex_del_private_types_non_mutex state.(EventState) /\
    task_stack_live_coverage state.(TskState) active /\
    state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) &&
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks)).

(** The existing initial-entry ABI supplies CPU/stack authority. The
    actual selector supplies current/ready; OSIntExit supplies nesting=0.
    Retaining the focused map here allows the foreign C body to return to
    the original Save, whose CPSID has not executed yet. *)
Lemma mutex_del_selected_initial_focused_entry : forall environment
  (entry : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg focus payload incoming selected node state,
  armv7a_initial_frame_binding selected -> selected.(armv7a_continuation_call) = None ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments) ->
  mutex_program_selected_reachable sg state -> mutex_del_private_types_non_mutex state.(EventState) ->
  state.(IntrState).(intNesting) = 0 ->
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  os_sched_source_selected_post environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
    environment.(mutex_del_call_port) environment.(mutex_del_call_continuations) sg
    focus incoming selected node state ** unmap_table_rep sg ** event_private_pool_rep sg state.(EventState) |--
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected state in
  coq_prop (mutex_del_call_stage call registered /\ registered.(IntrState).(intNesting) = 0) &&
  (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
     call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   mutex_del_focused_world environment.(mutex_del_call_continuations) sg focus payload
     (task_stack_call_active_key call) registered).
Proof.
  intros environment entry sg focus payload incoming selected node state Hbinding Hnone Hfragments
    Hreach Htypes Hnest Hlookup; cbv zeta.
  set (call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments)).
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
    exists node; exact (conj (proj1 Hready) Hgen). }
  unfold armv7a_task_restored_execution; rewrite Hnone.
  pose proof (armv7a_initial_call_register_resources _ _ _ environment.(mutex_del_call_continuations)
    entry sg state selected selected.(armv7a_continuation_fragments) Hbinding Hfragments Hcurrent) as Hregister.
  cbv zeta in Hregister; sep_apply_l_atomic Hregister; Intros.
  assert (Hsource : kernel_call_task_source call registered) by assumption.
  assert (Hstage : mutex_del_call_stage call registered).
  { unfold mutex_del_call_stage, call; cbn [armv7a_initial_call os_sched_call_origin].
    split; [exact Hsource|]. intros; exists node.
    cbn [armv7a_initial_call os_sched_call_stack]; rewrite Hlease.
    exact (conj (proj1 Hready) (proj2 (proj2 (proj2 (proj2 Hready))))). }
  assert (Hreachable : mutex_program_selected_reachable sg registered).
  { eapply mutex_program_source_step_reachable; [exact Hreach|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hcoverage : task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call)).
  { unfold task_stack_call_active_key, call, armv7a_initial_call; cbn [os_sched_call_origin].
    rewrite Hlease; exact Hcovered. }
  unfold mutex_del_focused_world; rewrite kernel_program_inv_split_unmap; fold call registered.
  change (armv7a_task_call_stacks environment.(mutex_del_call_continuations)
    registered.(TskState) focus registered.(TskState).(parkedTaskStacks)) with
    (armv7a_task_call_stacks environment.(mutex_del_call_continuations)
      state.(TskState) focus state.(TskState).(parkedTaskStacks)).
  entailer!.
Qed.

(** Reinsert the retained descriptor after actual selection of a different
    stack. Its physical bytes stayed in UCOS2_inv throughout selection. *)
Local Lemma mutex_del_retained_call_stack_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus retained,
  armv7a_continuation_binding retained -> armv7a_continuation_focus_binding focus retained ->
  task_stack_key retained.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
  armv7a_task_frame_slice retained ->
  task_stack_live_sp tasks (task_stack_key retained.(armv7a_continuation_stack))
    retained.(armv7a_continuation_sp) ->
  tasks.(parkedTaskStacks) (task_stack_key retained.(armv7a_continuation_stack)) =
    Some (retained.(armv7a_continuation_stack).(stackLeaseRegion), retained.(armv7a_continuation_fragments)) ->
  armv7a_dormant_continuation abi retained **
    armv7a_task_call_stacks abi tasks focus
      (task_stack_take tasks.(parkedTaskStacks) retained.(armv7a_continuation_stack)) |--
  armv7a_task_call_stacks abi tasks focus tasks.(parkedTaskStacks).
Proof.
  intros external platform port abi tasks focus retained Hbinding Hfocus Hkey Hslice Hsp Hlookup.
  sep_apply_l_atomic (armv7a_task_call_stacks_forget external platform port abi tasks focus
    (task_stack_take tasks.(parkedTaskStacks) retained.(armv7a_continuation_stack))).
  sep_apply_l_atomic (armv7a_task_call_stacks_park external platform port abi tasks focus
    (task_stack_take tasks.(parkedTaskStacks) retained.(armv7a_continuation_stack)) retained
    Hbinding Hfocus Hkey Hslice Hsp (task_stack_take_lookup _ _)).
  assert (Heq : task_stack_park_fragments
      (task_stack_take tasks.(parkedTaskStacks) retained.(armv7a_continuation_stack))
      retained.(armv7a_continuation_stack) retained.(armv7a_continuation_fragments) = tasks.(parkedTaskStacks)).
  { extensionality key; unfold task_stack_park_fragments, task_stack_take, field_update.
    destruct task_stack_key_eq_dec; [subst key; symmetry; exact Hlookup|reflexivity]. }
  rewrite Heq; reflexivity.
Qed.

(** Actual OSIntExit counter/selector/install/restore from the registry
    created by the interrupted Save's IRQ. The selected initial branch is
    consumed below; saved-call destinations retain their existing source
    obligation. No condition on future application execution is added. *)
Lemma mutex_del_irq_foreign_selected_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg state focus fragments handler before (frame : Assertion),
  let lease := focus.(armv7a_focus_call).(os_sched_call_stack) in
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true -> state.(SchedState).(readyList) <> [] ->
  (forall slot node, (os_int_exit_ready_checkpoint true state).(SchedState).(highRdyTid) = Some slot ->
    state.(TskState).(inUsedTaskStates) slot = Some node -> (slot, node.(taskGeneration)) <> task_stack_key lease) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  kernel_client_step external.(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true state) (os_int_exit_ready_checkpoint true state) ->
  (mutex_del_stack_registry abi sg focus (lease.(stackLeaseRegion), fragments) KernelClientHeapClosed state **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)) before ->
  exists prepared,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    (forall hooked, kernel_heap_execution [] prepared hooked ->
      exists transfer installed selected node,
        transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true state /\
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
        (forall final, armv7a_restore_transition abi handler selected installed final ->
          os_int_exit_source_selected_execution external platform port abi sg state handler transfer selected before final /\
          mutex_program_selected_reachable sg (os_int_exit_installed_state transfer) /\
          mutex_del_private_types_non_mutex (os_int_exit_installed_state transfer).(EventState) /\
          (os_int_exit_installed_state transfer).(IntrState).(intNesting) = 0 /\
          (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) =
            Some (lease.(stackLeaseRegion), fragments) /\
          (os_sched_source_selected_post external platform port abi sg focus
             transfer.(os_int_exit_incoming_stack) selected node (os_int_exit_installed_state transfer) **
           unmap_table_rep sg ** event_private_pool_rep sg (os_int_exit_installed_state transfer).(EventState) **
           (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) final)).
Proof.
  intros external platform port abi task_abi initial sg state focus fragments handler before frame lease
    Hrunning Hswitch Hnonempty Hdifferent Haddress Hhook Hpre.
  assert (Hopen : mutex_del_stack_registry abi sg focus (lease.(stackLeaseRegion), fragments)
      KernelClientHeapClosed state **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame) |--
    coq_prop (mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState) /\
      kernel_client_call_stack_facts focus (lease.(stackLeaseRegion), fragments) state) &&
    (UCOS2_inv sg state ** unmap_table_rep sg ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (event_private_pool_rep sg state.(EventState) ** frame)))).
  { unfold mutex_del_stack_registry, kernel_client_call_stack_resources, kernel_client_call_stack_world;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [[Hhistory [Htypes [Hcoverage Hlookup]]] Howned].
  assert (Hkey : task_stack_key lease = armv7a_call_focus_key focus) by reflexivity.
  match type of Howned with ?P before => assert (Hextract : P |-- EX retained,
    coq_prop (armv7a_continuation_binding retained /\ armv7a_continuation_focus_binding focus retained /\
      retained.(armv7a_continuation_stack) = lease /\ retained.(armv7a_continuation_fragments) = fragments /\
      armv7a_task_frame_slice retained /\ task_stack_live_sp state.(TskState) (task_stack_key lease)
        retained.(armv7a_continuation_sp)) &&
    (UCOS2_inv sg state ** unmap_table_rep sg **
     (armv7a_dormant_continuation abi retained ** armv7a_task_call_stacks abi state.(TskState) focus
       (task_stack_take state.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** (event_private_pool_rep sg state.(EventState) ** frame))))) end.
  { unfold armv7a_task_call_stacks.
    sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_call_stack_entry abi state.(TskState) focus)
      state.(TskState).(parkedTaskStacks) lease fragments Hlookup).
    fold (armv7a_task_call_stacks abi state.(TskState) focus (task_stack_take state.(TskState).(parkedTaskStacks) lease)).
    unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec; [|contradiction].
    Intros retained.
    assert (Hl : retained.(armv7a_continuation_stack) = lease).
    { assert (Hk : task_stack_key retained.(armv7a_continuation_stack) = task_stack_key lease) by tauto.
      assert (Hp : (retained.(armv7a_continuation_stack).(stackLeaseRegion), retained.(armv7a_continuation_fragments)) =
        (lease.(stackLeaseRegion), fragments)) by tauto.
      unfold task_stack_key in Hk; destruct retained.(armv7a_continuation_stack), lease; cbn in *; congruence. }
    assert (Hf : retained.(armv7a_continuation_fragments) = fragments).
    { assert (Hp : (retained.(armv7a_continuation_stack).(stackLeaseRegion), retained.(armv7a_continuation_fragments)) =
        (lease.(stackLeaseRegion), fragments)) by tauto; congruence. }
    Exists retained; rewrite Hl; entailer!; congruence. }
  destruct (Hextract before Howned) as [retained [[Hbinding [Hfocus [Hlease [Hfragments [Hslice Hsp]]]]] Hsplit]].
  destruct (armv7a_irq_switch_source_preserves_pending_split_initial_frame external platform port abi task_abi initial
    sg state retained focus handler (event_private_pool_rep sg state.(EventState) ** frame) before
    Hrunning Hswitch Hnonempty ltac:(rewrite Hlease; exact Hdifferent) Haddress Hcoverage Hhook Hsplit)
    as [prepared [Hprefix Hcontinue]].
  exists prepared; split; [exact Hprefix|]. intros hooked Hrun.
  destruct (Hcontinue hooked Hrun) as [transfer [installed [selected [node
    [Hstate [Hdestination [Hinstall [Hselected [Hfocused [Hready [Hgen [Hcovered [Hretained [Hinitial Hrestore]]]]]]]]]]]]]].
  assert (Hevent : (os_int_exit_installed_state transfer).(EventState) = state.(EventState)).
  { unfold os_int_exit_installed_state; rewrite Hstate; reflexivity. }
  assert (Hused : (os_int_exit_installed_state transfer).(TskState).(inUsedTaskStates) = state.(TskState).(inUsedTaskStates)).
  { unfold os_int_exit_installed_state; rewrite Hstate; reflexivity. }
  assert (Hhistory' : mutex_program_selected_reachable sg (os_int_exit_installed_state transfer)).
  { eapply mutex_program_source_step_reachable; [exact Hhistory|].
    apply MutexOwnerSourceFrame; [exact Hused|rewrite Hevent; reflexivity]. }
  assert (Hnest : (os_int_exit_installed_state transfer).(IntrState).(intNesting) = 0).
  { change (os_sched_requests_switch (os_int_exit_after_nesting state) = true) in Hswitch.
    destruct (proj1 (os_sched_requests_switch_iff _) Hswitch) as [Hselection _].
    pose proof (proj1 (proj1 (os_sched_selection_enabled_iff _) Hselection)) as Hz.
    unfold os_int_exit_installed_state; rewrite Hstate; exact Hz. }
  assert (Hlookup' : (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) =
    Some (lease.(stackLeaseRegion), fragments)).
  { rewrite Hlease, Hkey in Hretained; rewrite Hretained; exact Hlookup. }
  assert (Hmerge := mutex_del_retained_call_stack_merge external platform port abi
    (os_int_exit_installed_state transfer).(TskState) focus retained Hbinding Hfocus
    ltac:(rewrite Hlease; exact Hkey) Hslice ltac:(unfold task_stack_live_sp; rewrite Hused, Hlease; exact Hsp)
    ltac:(rewrite Hlease, Hfragments, Hkey; exact Hlookup')).
  exists transfer, installed, selected, node; split; [exact Hstate|]. split; [exact Hinstall|].
  split; [exact Hinitial|].
  intros final Hrestore_run; destruct (Hrestore final Hrestore_run) as [Hexecution Hfinal].
  split; [exact Hexecution|]. split; [exact Hhistory'|]. split; [rewrite Hevent; exact Htypes|].
  split; [exact Hnest|]. split; [exact Hlookup'|].
  match type of Hfinal with ?P final => match goal with |- ?Q final => assert (Hclose : P |-- Q) end end.
  { eapply derivable1_trans with (y :=
      (armv7a_dormant_continuation abi retained **
       armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
         (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
           retained.(armv7a_continuation_stack))) **
      (armv7a_task_restored_execution external platform port abi selected **
       UCOS2_inv sg (os_int_exit_installed_state transfer) ** unmap_table_rep sg **
       event_private_pool_rep sg state.(EventState) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)).
    - entailer!.
    - sep_apply_l_atomic Hmerge; unfold os_sched_source_selected_post; rewrite Hevent; entailer!. }
  exact (Hclose final Hfinal).
Qed.

Local Lemma mutex_del_focused_critical_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload active entry checkpoint eid option result,
  mutex_del_critical sg eid option entry result checkpoint ->
  coq_prop (mutex_program_selected_reachable sg entry /\ mutex_del_private_types_non_mutex entry.(EventState) /\
    task_stack_live_coverage entry.(TskState) active /\
    entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) &&
  (kernel_program_inv sg checkpoint ** event_private_pool_rep sg entry.(EventState) **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks)) |--
  mutex_del_focused_world abi sg focus payload active checkpoint.
Proof.
  intros external platform port abi sg focus payload active entry checkpoint eid option result Hrun.
  Intros_p Hfacts; destruct Hfacts as [Hhistory [Htypes [Hcoverage Hfocus]]].
  destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hrun)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  assert (Hcoverage' : task_stack_live_coverage checkpoint.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame; [|exact Hstacks|exact Hcoverage].
    intros slot node Hnode; specialize (Hnodes slot); rewrite Hnode in Hnodes.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    cbn in Hnodes; injection Hnodes as Hg Hsp; exists old; auto. }
  assert (Hhistory' : mutex_program_selected_reachable sg checkpoint).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_program_del_critical_source; exact Hrun. }
  assert (Htypes' : mutex_del_private_types_non_mutex checkpoint.(EventState)).
  { unfold mutex_del_private_types_non_mutex in *; rewrite Hprivate; exact Htypes. }
  sep_apply_l_atomic (mutex_del_call_stacks_critical_reindex external platform port abi sg eid option
    entry result checkpoint focus Hrun).
  unfold mutex_del_focused_world, event_private_pool_rep; rewrite Hprivate; entailer!;
    rewrite Hstacks; exact Hfocus.
Qed.

(** This body is executed by the foreign task established above. Its CPU
    and critical token remain linear outside the shared body owner, while
    the original interrupted invocation stays parked in the focused map. *)
Lemma mutex_del_focused_always_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload active call eid entry prepared event mutex
  before prepared_heap after (frame : Assertion),
  mutex_del_parent_layout sg -> valid_event_id sg eid ->
  mutex_del_parent_entry sg eid entry event mutex -> mutex_del_call_stage call entry ->
  (mutex_del_focused_world abi sg focus payload active entry ** frame) before ->
  mutex_del_prepare_source_execution sg (event_addr sg eid) eid entry prepared before prepared_heap ->
  mutex_del_always_after_prepare_execution sg (event_addr sg eid) prepared_heap after ->
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  mutex_del_critical sg eid 1 entry
    (0, (OS_ERR_NONE, negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0))) checkpoint /\
  mutex_del_call_stage call checkpoint /\
  (mutex_del_focused_world abi sg focus payload active checkpoint ** frame) after.
Proof.
  intros external platform port abi sg focus payload active call eid entry prepared event mutex before prepared_heap
    after frame Hlayout Hid Hparent Hstage Hpre Hprepare Hbody checkpoint.
  assert (Hopen : mutex_del_focused_world abi sg focus payload active entry ** frame |--
    coq_prop (mutex_program_selected_reachable sg entry /\ mutex_del_private_types_non_mutex entry.(EventState) /\
      task_stack_live_coverage entry.(TskState) active /\
      entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) &&
    (kernel_program_inv sg entry **
      (event_private_pool_rep sg entry.(EventState) **
       armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_focused_world; entailer!. }
  destruct (Hopen before Hpre) as [Hfacts Howned].
  pose proof (mutex_del_prepare_source_resources sg eid entry prepared event mutex before prepared_heap
    _ Hlayout Hparent Howned Hprepare) as Hprepared.
  destruct (mutex_del_always_after_prepare_resources sg eid entry prepared event mutex prepared_heap after _
    (event_table_layout_select sg eid (proj1 (proj2 Hlayout)) Hid) Hprepared Hbody) as [Hcritical Hafter].
  split; [exact Hcritical|]. split.
  - eapply mutex_del_critical_preserves_call_stage; eassumption.
  - assert (Hmerge : kernel_program_inv sg checkpoint ** event_private_pool_rep sg entry.(EventState) **
      armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
      mutex_del_focused_world abi sg focus payload active checkpoint).
    { intros heap Hheap; apply (mutex_del_focused_critical_merge external platform port abi sg focus payload
        active entry checkpoint eid 1 _ Hcritical); split; assumption. }
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { eapply derivable1_trans with (y :=
        (kernel_program_inv sg checkpoint ** event_private_pool_rep sg entry.(EventState) **
         armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks)) ** frame).
      - unfold checkpoint; entailer!.
      - sep_apply_l_atomic Hmerge; entailer!. }
    exact (Hclose after Hafter).
Qed.

(** A complete local no-wait ALWAYS path after the successful ordered C
    prefix: actual MRS/CPSID suffix, protected body, Restore/BX and perr
    store. No scheduler call occurs on this observed zero-wait branch.
    Interrupts before/after this branch use separate actual producers. *)
Lemma mutex_del_foreign_local_delete_post : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg focus payload call mask entry eid event mutex registers final_registers acquired prepared
  before saved_heap body_heap prepared_heap recycled cursor written middle final_cursor returned after perr old_error cpu_sr
  (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  mutex_del_parent_layout sg -> valid_event_id sg eid ->
  mutex_del_parent_entry sg eid entry event mutex -> mutex_del_call_stage call entry ->
  mutex_del_parent_prefix_ok (event_addr sg eid) entry eid ->
  encode_event_wait_grp event.(waitList) entry.(TskState) = 0 ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      call mask ** mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) entry **
    ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame)) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry before final_registers acquired saved_heap ->
  kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) saved_heap body_heap ->
  mutex_del_prepare_source_execution sg (event_addr sg eid) eid entry prepared body_heap prepared_heap ->
  mutex_del_always_after_prepare_execution sg (event_addr sg eid) prepared_heap recycled ->
  cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor recycled written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor returned ->
  kernel_heap_execution [(perr, 0)] returned after ->
  acquired = entry /\
  kernel_call_save_uninterrupted_execution arch registers entry before final_registers acquired saved_heap /\
  mutex_del_critical sg eid 1 entry (0, (OS_ERR_NONE, false)) checkpoint /\
  mutex_del_call_stage call checkpoint /\
  (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
     call mask ** mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) checkpoint **
    ((perr # UChar |-> 0) ** (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** frame)) after /\
  (mutex_del_runtime_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
     sg call mask entry (event_addr sg eid) 1 eid 0 0 ** (perr # UChar |-> 0) **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** frame) after.
Proof.
  intros environment critical arch save restore sg focus payload call mask entry eid event mutex registers
    final_registers acquired prepared before saved_heap body_heap prepared_heap recycled cursor written middle final_cursor
    returned after perr old_error cpu_sr frame abi checkpoint Hlayout Hid Hparent Hstage Hprefix Hwait Hnone Hvalid Hmask
    Hpre Hsave Hcpu_store Hprepare Hbody Hr0 Hmasked Hrestore_prefix Hrestore_suffix Herror.
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid|reflexivity]).
  assert (Hsave_pre : (kernel_call_execution_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
      (mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) entry **
       ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame))) before).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask.
    match type of Hpre with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder before Hpre). }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call (kernel_save_read_cpsr registers)
    entry before final_registers acquired saved_heap _ Hsaved Hsave_pre Hsave)
    as [Hacquired [Hmemory [Hreturn [Hword Hsaved_heap]]]].
  cbn [kernel_save_read_cpsr kernel_save_r0] in Hword.
  match type of Hsaved_heap with ?P saved_heap => assert (Hcpu_pre : P |--
    (cpu_sr # UInt |->_) **
    (mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) entry **
     critical_region_masked environment.(mutex_del_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
     os_sched_context_resources environment.(mutex_del_call_external) call **
     ((perr # UChar |-> old_error) ** frame))) by entailer! end.
  destruct (task_stack_uint_store_execution cpu_sr final_registers.(kernel_save_r0) _ saved_heap
    ltac:(rewrite Hword; exact Hvalid) (Hcpu_pre saved_heap Hsaved_heap)) as [stored [Hstored Hbody_heap]].
  assert (stored = body_heap) by (eapply kernel_heap_execution_deterministic; eassumption); subst stored.
  match type of Hbody_heap with ?P body_heap => assert (Hbody_pre : P |--
    mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) entry **
    (critical_region_masked environment.(mutex_del_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
     os_sched_context_resources environment.(mutex_del_call_external) call **
     ((perr # UChar |-> old_error) ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** frame))) by entailer! end.
  destruct (mutex_del_focused_always_resources _ _ _ abi sg focus payload (task_stack_call_active_key call)
    call eid entry prepared event mutex body_heap prepared_heap recycled _ Hlayout Hid Hparent Hstage
    (Hbody_pre body_heap Hbody_heap) Hprepare Hbody) as [Hcritical [Hstage_after Hrecycled]].
  rewrite Hwait in Hcritical; cbn [Z.eqb negb] in Hcritical.
  match type of Hrecycled with ?P recycled => assert (Hrestore_pre : P |--
    critical_region_masked environment.(mutex_del_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
    os_sched_context_resources environment.(mutex_del_call_external) call **
    (mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) checkpoint **
     ((perr # UChar |-> old_error) ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) ** frame)))
       by (unfold checkpoint; entailer!) end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call
    final_registers.(kernel_save_r0) entry cursor recycled written middle final_cursor returned _ Hr0 Hmasked
    (Hrestore_pre recycled Hrecycled) Hrestore_prefix Hrestore_suffix)
    as [Hrestore [Hreturn_word [Hrestore_memory Hreturned]]].
  cbn [kernel_save_read_cpsr kernel_save_r0] in Hword; rewrite Hword, Hmask in Hreturned.
  match type of Hreturned with ?P returned => assert (Hstore_pre : P |--
    (perr # UChar |-> old_error) **
    (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
       call mask ** mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) checkpoint **
       (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** frame))
      by entailer! end.
  destruct (kernel_heap_framed_uchar_store perr old_error 0 _ returned ltac:(lia)
    (Hstore_pre returned Hreturned)) as [produced [Hwrite Hwritten]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hafter : (kernel_call_execution_owned environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) call mask **
    mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) checkpoint **
    ((perr # UChar |-> 0) ** (cpu_sr # UInt |-> registers.(kernel_save_cpsr)) ** frame)) after).
  { match type of Hwritten with ?P after => match goal with |- ?Q after => assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder after Hwritten). }
  split; [exact Hacquired|]. split.
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hnone|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  split; [exact Hcritical|]. split; [exact Hstage_after|]. split; [exact Hafter|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpublic : P |-- Q) end end.
  { unfold mutex_del_runtime_post; Left; Right; Exists entry checkpoint 0.
    unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists call checkpoint environment.
    unfold mutex_del_focused_world; Intros.
    sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ abi checkpoint.(TskState) focus
      checkpoint.(TskState).(parkedTaskStacks)).
    unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources, mutex_del_callsite_environment,
      kernel_stack_call_same_call.
    entailer!.
    - constructor.
    - exists OS_ERR_NONE, false; exact (conj Hcritical (conj eq_refl eq_refl)). }
  exact (Hpublic after Hafter).
Qed.

(** A real subsequent IRQ parks the executing foreign call. Its coverage
    becomes None only after the ABI save and actual nesting/TCB-SP stores;
    the original pending call remains focused. This is the entry consumed
    by the existing creator/private-pool trace, rather than an ISR Del. *)
Lemma mutex_del_foreign_irq_registry : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication focus payload (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice saved ->
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
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  (os_int_exit_frame_save_pre external platform handler **
    (mutex_del_focused_world abi sg focus payload (Some (task_stack_key call.(os_sched_call_stack))) entry ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed parked **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)) registry_heap.
Proof.
  intros external platform port abi sg entry node handler saved publication focus payload frame before saved_heap
    call parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hpre Hsave.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg entry /\ mutex_del_private_types_non_mutex entry.(EventState) /\
      task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
      entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) &&
    (os_int_exit_frame_save_pre external platform handler **
     (UCOS2_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
      (unmap_table_rep sg ** event_private_pool_rep sg entry.(EventState) ** frame)))) end.
  { unfold mutex_del_focused_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [[Hhistory [Htypes [Hcoverage Hfocus]]] Howned].
  destruct (armv7a_irq_source_save_preserves_pending_call external platform port abi sg entry node handler saved
    publication focus payload (unmap_table_rep sg ** event_private_pool_rep sg entry.(EventState) ** frame)
    before saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Howned Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered [Hkept [Hsplit [Hmap Hother_focus]]]]]]].
  assert (Hevent : parked.(EventState) = entry.(EventState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Hhistory' : mutex_program_selected_reachable sg parked).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_program_task_fields_source with (tid := call.(os_sched_call_stack).(stackLeaseSlot))
      (old := node) (new := task_set_saved_sp node saved.(armv7a_continuation_sp));
      [exact Hnode|reflexivity|reflexivity| |rewrite Hevent; reflexivity].
    unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  match type of Hmap with ?P registry_heap => match goal with |- ?Q registry_heap => assert (Hclose : P |-- Q) end end.
  { unfold mutex_del_stack_registry, kernel_client_call_stack_resources,
      kernel_client_call_stack_world, kernel_client_call_stack_facts.
    rewrite kernel_program_inv_split_unmap; rewrite Hevent; entailer!. }
  exact (Hclose registry_heap Hmap).
Qed.

(** Consume the foreign deletion's SAME recycled state, its returned CPU
    and focused map. A subsequent real IRQ deposits the foreign frame;
    the already checked Sem/Mbox creator trace can reuse that ECB. The
    final Type byte is read from its current owner, including a creator's
    private image. Returning to the original Save remains a distinct ABI
    restore/suffix consumer; no CPU ownership is fabricated at this cut. *)
Lemma mutex_del_foreign_recycle_irq_recheck : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients actor creator sg observer origin
  eid event prepared node handler saved publication focus payload before saved_heap
  (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  let parked := armv7a_irq_live_parked_state checkpoint call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  valid_event_id sg eid ->
  armv7a_task_frame_slice saved ->
  checkpoint.(SchedState).(isRunning) = true -> checkpoint.(IntrState).(intNesting) = 0 ->
  checkpoint.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  checkpoint.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  checkpoint.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened checkpoint.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  (kernel_call_execution_owned external platform call handler.(os_int_exit_interrupted_mask) **
    mutex_del_focused_world abi sg focus payload (Some (task_stack_key call.(os_sched_call_stack))) checkpoint **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg checkpoint
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall next after,
      kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
        KernelClientHeapClosed registry_heap next after ->
      exists returned returned_origin kind,
        kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
          KernelClientHeapClosed parked next returned /\
        kernel_resumption_task_source_trace external port clients sg observer None origin
          parked false returned_origin returned /\
        mutex_owner_source_history sg parked returned /\
        uchar_load (event_addr sg eid) kind after /\
        mutex_del_runtime_type_observation sg eid returned kind /\ kind <> 4 /\
        (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed returned **
          (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
           os_int_exit_context_resources port handler ** frame)) after).
Proof.
  intros external platform port abi clients actor creator sg observer origin eid event prepared node handler saved
    publication focus payload before saved_heap frame call checkpoint parked Hid Hslice Hrunning Hnest Hcurrent
    Hnode Hnode_id Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hinclude Hforeign Harguments Hpre Hsave.
  match type of Hpre with ?P before => assert (Hirq_pre : P |--
    os_int_exit_frame_save_pre external platform handler **
    (mutex_del_focused_world abi sg focus payload (Some (task_stack_key call.(os_sched_call_stack))) checkpoint ** frame))
      by (unfold os_int_exit_frame_save_pre, call; entailer!) end.
  destruct (mutex_del_foreign_irq_registry external platform port abi sg checkpoint node handler saved publication
    focus payload frame before saved_heap Hslice Hrunning Hnest Hcurrent Hnode Hnode_id Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp (Hirq_pre before Hpre) Hsave)
    as [registry_heap [Hwrites [Hstores Hregistry]]].
  assert (Hevent : parked.(EventState) = checkpoint.(EventState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Hnonmutex : forall current, parked.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) <> OS_EVENT_TYPE_MUTEX).
  { intros current Hget; rewrite Hevent in Hget.
    unfold checkpoint in Hget; cbn [mutex_del_always_checkpoint mutex_del_recycle_state replace_EventS
      EventState event_recycle inUsedEventStates] in Hget.
    rewrite kernel_map_set_same in Hget; discriminate. }
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros next after Htrace.
  destruct (mutex_del_stack_creator_trace external platform port abi clients actor creator sg observer focus payload
    KernelClientHeapClosed registry_heap next after _ Hinclude Hforeign Harguments Htrace parked origin I Hregistry)
    as [returned [returned_origin [Hstates [Hsource [Hcut Hafter]]]]].
  assert (Hnonmutex_returned : forall current, returned.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) <> OS_EVENT_TYPE_MUTEX).
  { eapply mutex_del_creator_trace_preserves_non_mutex_slot; eassumption. }
  destruct (mutex_del_registry_non_mutex_type_load external platform port abi sg focus payload next returned eid after
    _ Hid (mutex_del_creator_trace_preserves_return_cut creator sg _ _ _ _ Hstates I) Hnonmutex_returned Hafter)
    as [kind [Hload [Hobs [Hkind Hclosed]]]].
  exists returned, returned_origin, kind; split; [exact Hstates|]. split; [exact Hsource|].
  split; [eapply mutex_del_creator_trace_owner_history; exact Hstates|].
  split; [exact Hload|]. split; [exact Hobs|]. split; assumption.
Qed.

(** Return to the original MRS+4 cursor. The selected frame supplies the
    actual restored CPSR/R0/LR; there is no saved critical token for this
    Save yet. Only its real CPSID/DSB/BX suffix creates that token. The
    private ECB pool here is the CURRENT pool after foreign execution. *)
Lemma mutex_del_first_save_irq_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg initial state handler original suspended saved_word before (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  let checkpoint := os_int_exit_ready_checkpoint true state in
  let cached := replace_SchedS (sched_install_selected checkpoint.(SchedState)) checkpoint in
  let current := os_int_exit_wrapper_restored_state cached original.(os_sched_call_stack) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  suspended.(armv7a_continuation_pc) = armv7a_save_entry_address save + 4 ->
  nth 0 suspended.(armv7a_continuation_registers) 0 = saved_word ->
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word ->
  mutex_owner_source_history sg initial state ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  state.(SchedState).(isRunning) = true -> os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  checkpoint.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg checkpoint checkpoint ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state **
    (interrupt_platform_running environment.(mutex_del_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(mutex_del_call_port) handler ** frame)) before ->
  exists prepared installed selected,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    kernel_heap_execution [] prepared prepared /\
    sched_install_heap_fragment sg prepared installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    armv7a_continuation_focus_binding focus selected /\
    selected.(armv7a_continuation_pc) = armv7a_save_entry_address save + 4 /\
    (forall irq_return registers final_registers acquired after,
      armv7a_restore_transition abi handler selected installed irq_return ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      armv7a_save_suffix_transition save registers current irq_return final_registers acquired after ->
      acquired = current /\ final_registers.(kernel_save_r0) = saved_word /\
      final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
      (mutex_del_source_save_post environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) critical sg original
         (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) after /\
      (kernel_stack_call_masked abi mutex_del_stack_resources critical sg
         (task_stack_call_active_key original) (armv7a_continuation_resumed_call selected original)
         saved_word current current **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) after).
Proof.
  intros environment critical arch save sg initial state handler original suspended saved_word before frame abi
    focus payload checkpoint cached current Horigin Hbinding Hcall Hslice Hpc Hr0 Hsaved Hhistory Hactive Hpointer
    Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  destruct Hpointer as [node [Hnode [Hgen Hsp]]]; rewrite Hlease in Hnode, Hgen.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState) /\
      kernel_client_call_stack_facts focus payload state) &&
    (UCOS2_inv sg state ** unmap_table_rep sg **
     (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running environment.(mutex_del_call_platform)
         handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources environment.(mutex_del_call_port) handler **
       (event_private_pool_rep sg state.(EventState) ** frame))))) end.
  { unfold mutex_del_stack_registry, kernel_client_call_stack_resources, kernel_client_call_stack_world;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [[Hreach [Htypes Hfacts]] Howned].
  destruct (os_int_exit_source_switch_prefix_frame_post sg state _ before Hrunning Hswitch Hnonempty Howned)
    as [prepared [Hprefix [Hconsistent Hprepared]]].
  fold checkpoint in Hprepared, Hconsistent.
  assert (Hvalid : UCOS2_state_inv sg checkpoint).
  { match type of Hprepared with ?P prepared => assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg checkpoint) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose prepared Hprepared)). }
  assert (Hready : is_effectively_ready node.(stat) node.(dly) = true).
  { pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hmembers.
    pose proof Hconsistent as Hselected; unfold sched_high_ready_consistency in Hselected.
    destruct checkpoint.(SchedState).(readyList) as [|slot tail] eqn:Hlist.
    - destruct Hselected as [Hnone _]; congruence.
    - destruct Hselected as [Hslot [head [Hhead Hpriority]]].
      assert (slot = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst slot.
      destruct (Hmembers _ (or_introl eq_refl)) as [found [Hfound [_ Hready]]].
      change (state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some found) in Hfound.
      assert (found = node) by congruence; subst found; exact Hready. }
  assert (Hindex : forall p, checkpoint.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p).
  { intros p Hp; unfold sched_high_ready_consistency in Hconsistent.
    destruct checkpoint.(SchedState).(readyList) as [|slot tail] eqn:Hlist.
    - destruct Hconsistent as [Hnone _]; congruence.
    - destruct Hconsistent as [Hslot [selected_node [Hselected_node Hpriority]]].
      assert (slot = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst slot.
      assert (selected_node = node) by
        (change (state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some selected_node)
          in Hselected_node; congruence).
      subst selected_node; assert (p = node.(curPrio)) by congruence; subst p.
      pose proof (proj1 (proj2 Hvalid)) as Htasks.
      assert (Hrange : forall tid t, checkpoint.(TskState).(inUsedTaskStates) tid = Some t ->
        task_priority_in_range sg t.(curPrio)) by (unfold task_in_range in Htasks; tauto).
      apply (Hrange _ _ Hnode). }
  match type of Hprepared with ?P prepared => assert (Hraw : P |-- UCOS2_raw_rep sg checkpoint **
    (unmap_table_rep sg ** armv7a_task_call_stacks abi checkpoint.(TskState) focus checkpoint.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(mutex_del_call_platform)
        handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources environment.(mutex_del_call_port) handler **
      (event_private_pool_rep sg state.(EventState) ** frame)))) end.
  { unfold UCOS2_inv; entailer!. }
  destruct (sched_install_heap_raw_frame_post sg checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    node _ prepared Hhigh Hnode Haddress (Hraw prepared Hprepared)) as [installed [Hinstall Hinstalled]].
  assert (Hcached_valid : UCOS2_state_inv sg cached)
    by (apply os_int_exit_install_cache_preserves_validity; assumption).
  match type of Hinstalled with ?P installed => assert (Hclosed : P |-- kernel_client_call_stack_world abi sg focus payload cached **
    (interrupt_platform_running environment.(mutex_del_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(mutex_del_call_port) handler **
     (event_private_pool_rep sg state.(EventState) ** frame))) end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!. }
  assert (Hpointer : task_saved_pointer_at cached suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)).
  { exists node; rewrite Hlease; auto. }
  destruct (task_create_pending_call_stack_restore _ _ _ abi sg original suspended Hbinding Hcall Hslice
    cached installed handler _ Hpointer Hhigh Haddress (Hclosed installed Hinstalled))
    as [selected [Hpointers [Hfocused [Hselected_lease [Hselected_sp [Hcpsr [Hregisters [Hcoverage Hresume]]]]]]]].
  assert (Hsame : kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original).
  { unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hstage : mutex_del_call_stage original current).
  { unfold mutex_del_call_stage; rewrite Horigin; split.
    - unfold kernel_call_task_source; split; [exact Horigin|]. split; [exact Hactive|].
      unfold task_execution_current; rewrite Horigin; exact Hhigh.
    - intros; exists node; exact (conj Hnode Hready). }
  assert (Hreach_current : mutex_program_selected_reachable sg current).
  { eapply mutex_program_source_step_reachable; [exact Hreach|]. apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hhistory_current : mutex_owner_source_history sg initial current).
  { eapply mutex_owner_source_history_trans; [exact Hhistory|].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity. }
  exists prepared, installed, selected; split; [exact Hprefix|]. split; [split; [constructor|auto]|].
  split; [rewrite Hselected_sp, <- Hsp; exact Hinstall|].
  split; [exact Hcpsr|]. split; [exact Hregisters|]. split; [exact Hfocused|].
  split.
  { destruct Hfocused as [_ [Hselected_pc _]].
    cbn [focus armv7a_call_focus armv7a_focus_pc] in Hselected_pc; congruence. }
  intros irq_return registers final_registers acquired after Hirq Hreg0 Hregcpsr Hreglr Hsuffix.
  destruct (Hresume irq_return Hirq) as [Hmemory Hrestored].
  assert (Hword : registers.(kernel_save_r0) = saved_word) by (rewrite Hreg0, Hregisters; exact Hr0).
  assert (Hmask : armv7a_irq_fiq_mask registers.(kernel_save_cpsr) =
    armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) by (rewrite Hregcpsr, Hcpsr; reflexivity).
  assert (Hsaved_current : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    registers.(kernel_save_r0)) by (rewrite Hword, Hmask; exact Hsaved).
  match type of Hrestored with ?P irq_return => assert (Hsuffix_pre : P |--
    kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
    (kernel_stack_inv abi mutex_del_stack_resources sg (task_stack_call_active_key original) current **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))) end.
  { unfold kernel_stack_inv, mutex_del_stack_resources; rewrite kernel_program_inv_split_unmap.
    fold current.
    change (event_private_pool_rep sg current.(EventState)) with (event_private_pool_rep sg state.(EventState)).
    unfold task_stack_call_active_key; rewrite Horigin, Hmask; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg
    (armv7a_continuation_resumed_call selected original) registers current irq_return final_registers acquired after
    _ Hsaved_current (Hsuffix_pre irq_return Hrestored) Hsuffix) as [Hacquired [Hmem [Hreturn [Hfinal_word Hafter]]]].
  assert (Hlr : registers.(kernel_save_lr) = suspended.(armv7a_continuation_lr)).
  { destruct Hfocused as [_ [_ Hlr]]; cbn [focus armv7a_call_focus armv7a_focus_lr] in Hlr; congruence. }
  split; [exact Hacquired|]. split; [rewrite Hfinal_word; exact Hword|].
  split; [rewrite Hreturn, Hlr; reflexivity|].
  assert (Hpost : kernel_stack_call_masked abi mutex_del_stack_resources critical sg
      (task_stack_call_active_key original) (armv7a_continuation_resumed_call selected original)
      saved_word current current |--
    mutex_del_source_save_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      critical sg original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial).
  { apply mutex_del_source_save_post_from_masked; assumption. }
  assert (Hmasked : (kernel_stack_call_masked abi mutex_del_stack_resources critical sg
      (task_stack_call_active_key original) (armv7a_continuation_resumed_call selected original)
      saved_word current current **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) after).
  { match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
    { unfold kernel_stack_call_masked; rewrite Hfinal_word, Hword; entailer!. }
    exact (Hfinish after Hafter). }
  split; [|exact Hmasked].
  match type of Hmasked with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { apply derivable1_sepcon_mono; [exact Hpost|reflexivity]. }
  exact (Hfinish after Hmasked).
Qed.

Section FirstSaveRecheckReturn.
Context (environment : MutexDelCallEnvironment) (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).

(** Concrete consumer of the returning first-Save producer: store its
    actual R0 into cpu_sr, reread Type from the current physical owner,
    take the non-Mutex C guard, Restore and write OS_ERR_EVENT_TYPE.
    The Type guard is an observed branch of the actual execution; it is
    not a precondition excluding the fresh-Mutex reuse branch. *)
Lemma mutex_del_first_save_recheck_error_post : forall critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  initial state handler original suspended saved_word before eid option perr old_error cpu_sr (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  let checkpoint := os_int_exit_ready_checkpoint true state in
  let current := os_int_exit_wrapper_restored_state
    (replace_SchedS (sched_install_selected checkpoint.(SchedState)) checkpoint) original.(os_sched_call_stack) in
  valid_event_id sg eid -> mutex_del_parent_prefix_ok (event_addr sg eid) initial eid ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  suspended.(armv7a_continuation_pc) = armv7a_save_entry_address save + 4 ->
  nth 0 suspended.(armv7a_continuation_registers) 0 = saved_word ->
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word ->
  mutex_owner_source_history sg initial state ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  state.(SchedState).(isRunning) = true -> os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  checkpoint.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg checkpoint checkpoint ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state **
    (interrupt_platform_running environment.(mutex_del_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(mutex_del_call_port) handler **
     ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame))) before ->
  exists prepared installed selected,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    sched_install_heap_fragment sg prepared installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    (forall irq_return registers final_registers acquired resumed stored kind,
      armv7a_restore_transition abi handler selected installed irq_return ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      armv7a_save_suffix_transition save registers current irq_return final_registers acquired resumed ->
      kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) resumed stored ->
      uchar_load (event_addr sg eid + OSEventType_off) kind stored -> kind <> 4 ->
      exists observed actual,
        mutex_del_runtime_type_observation sg eid observed kind /\
        mutex_del_runtime_save_facts sg (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
          saved_word initial observed /\
        kernel_stack_call_same_call actual original /\
        (forall restore_entry cursor written released returned final restored final_cursor exited after,
          cursor.(kernel_restore_r0) = saved_word ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor stored written released ->
          mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
            handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments)
            (armv7a_irq_fiq_mask saved_word) (restore_entry + 8) cursor.(kernel_restore_lr)
            actual observed released returned final restored ->
          armv7a_restore_suffix_transition restore written restored final_cursor exited ->
          kernel_heap_execution [(perr, encode_os_err_code OS_ERR_EVENT_TYPE)] exited after ->
          final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
          (mutex_del_runtime_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
             sg original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) initial
             (event_addr sg eid) option eid (event_addr sg eid) (encode_os_err_code OS_ERR_EVENT_TYPE) **
           (perr # UChar |-> encode_os_err_code OS_ERR_EVENT_TYPE) ** (cpu_sr # UInt |-> saved_word) **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after)).
Proof.
  intros critical arch save restore initial state handler original suspended saved_word before eid option perr old_error
    cpu_sr frame abi focus payload checkpoint current Hid Hprefix Horigin Hbinding Hcall Hslice Hpc Hr0 Hsaved Hhistory
    Hactive Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre.
  destruct (mutex_del_first_save_irq_return_source environment critical arch save sg initial state handler original
    suspended saved_word before ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame)
    Horigin Hbinding Hcall Hslice Hpc Hr0 Hsaved Hhistory Hactive Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre)
    as (prepared & installed & selected & Hselect & Hempty & Hinstall & Hcpsr & Hvalues & Hfocus & Hentry & Hreturn).
  exists prepared, installed, selected; split; [exact Hselect|]. split; [exact Hinstall|].
  intros irq_return registers final_registers acquired resumed stored kind Hirq Hreg0 Hregcpsr Hreglr Hsuffix
    Hstore Htype Hnot.
  destruct (Hreturn irq_return registers final_registers acquired resumed Hirq Hreg0 Hregcpsr Hreglr Hsuffix)
    as [Hacquired [Hword [Hlr [Hreturned Hmasked]]]].
  rewrite Hword in Hstore.
  match type of Hreturned with ?P resumed => assert (Hstore_pre : P |-- (cpu_sr # UInt |->_) **
    (mutex_del_source_save_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
       critical sg original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial **
     (perr # UChar |-> old_error) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))
    by entailer! end.
  destruct (task_stack_uint_store_execution cpu_sr saved_word _ resumed (proj1 Hsaved) (Hstore_pre resumed Hreturned))
    as [produced [Hwrite Hwritten]].
  assert (produced = stored) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  match type of Hwritten with ?P stored => assert (Hrecheck_pre : P |--
    mutex_del_source_save_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
       critical sg original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial **
     (perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved_word) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
    by entailer! end.
  exact (mutex_del_recheck_error_source_post environment sg Local local_step normal_return handler_contract
    handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) critical arch restore original
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial (event_addr sg eid) eid option kind
    perr old_error cpu_sr stored frame eq_refl Hid Hprefix (Hrecheck_pre stored Hwritten) Htype Hnot).
Qed.
End FirstSaveRecheckReturn.
