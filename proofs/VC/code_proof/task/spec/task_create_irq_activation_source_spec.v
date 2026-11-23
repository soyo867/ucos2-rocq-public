Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_focused_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reinsert the exact retained descriptor after selection of a different
    task. This is the same map split/merge used by the Mutex source owner;
    only the descriptor at its existing key is reinserted. *)
Local Lemma task_retained_call_stack_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus retained,
  armv7a_continuation_binding retained -> armv7a_continuation_focus_binding focus retained ->
  task_stack_key retained.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
  armv7a_task_frame_slice retained ->
  task_stack_live_sp tasks (task_stack_key retained.(armv7a_continuation_stack))
    retained.(armv7a_continuation_sp) ->
  tasks.(parkedTaskStacks) (task_stack_key retained.(armv7a_continuation_stack)) =
    Some (retained.(armv7a_continuation_stack).(stackLeaseRegion), retained.(armv7a_continuation_fragments)) ->
  armv7a_dormant_continuation abi retained ** armv7a_task_call_stacks abi tasks focus
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

(** Consume the real IRQ control resources at OSIntCtxSw. They become the
    selected task's execution resources; only the handler's physical stack
    is returned as a frame. The caller's focused map, reservation/history
    and exact saved SP survive the actual selector/install transition.
    The different-key observation identifies this source branch. *)
Lemma task_irq_foreign_selected_source : forall external platform port
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
  (kernel_client_call_stack_world abi sg focus (lease.(stackLeaseRegion), fragments) state **
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
          let current := os_int_exit_installed_state transfer in
          os_int_exit_source_selected_execution external platform port abi sg state handler transfer selected before final /\
          current.(SchedState).(isRunning) = true /\ current.(IntrState).(intNesting) = 0 /\
          current.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some (lease.(stackLeaseRegion), fragments) /\
          current.(TskState).(parkedTaskStacks) (task_stack_key transfer.(os_int_exit_incoming_stack)) = None /\
          (forall saved_stack sp, task_saved_pointer_at state saved_stack sp -> task_saved_pointer_at current saved_stack sp) /\
          (forall invocation, task_tcb_init_call_preserved sg invocation state current) /\
          (os_sched_source_selected_post external platform port abi sg focus
             transfer.(os_int_exit_incoming_stack) selected node current ** unmap_table_rep sg **
           (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) final)).
Proof.
  intros external platform port abi task_abi initial sg state focus fragments handler before frame lease
    Hrunning Hswitch Hnonempty Hdifferent Haddress Hhook Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (kernel_client_call_stack_facts focus (lease.(stackLeaseRegion), fragments) state) &&
    (UCOS2_inv sg state ** unmap_table_rep sg ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame))) end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [[Hcoverage Hlookup] Howned].
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
        os_int_exit_context_resources port handler ** frame)))) end.
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
    sg state retained focus handler frame before Hrunning Hswitch Hnonempty
    ltac:(rewrite Hlease; exact Hdifferent) Haddress Hcoverage Hhook Hsplit)
    as [prepared [Hprefix Hcontinue]].
  exists prepared; split; [exact Hprefix|]. intros hooked Hrun.
  destruct (Hcontinue hooked Hrun) as [transfer [installed [selected [node
    [Hstate [Hdestination [Hinstall [Hselected [Hfocused [Hready [Hgen [Hcovered [Hretained [Hinitial Hrestore]]]]]]]]]]]]]].
  set (current := os_int_exit_installed_state transfer).
  fold current in Hretained.
  assert (Hused : current.(TskState).(inUsedTaskStates) = state.(TskState).(inUsedTaskStates)).
  { unfold current, os_int_exit_installed_state; rewrite Hstate; reflexivity. }
  assert (Hnest : current.(IntrState).(intNesting) = 0).
  { change (os_sched_requests_switch (os_int_exit_after_nesting state) = true) in Hswitch.
    destruct (proj1 (os_sched_requests_switch_iff _) Hswitch) as [Hselection _].
    pose proof (proj1 (proj1 (os_sched_selection_enabled_iff _) Hselection)) as Hz.
    unfold current, os_int_exit_installed_state; rewrite Hstate; exact Hz. }
  assert (Hlookup' : current.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) =
    Some (lease.(stackLeaseRegion), fragments)).
  { rewrite Hlease, Hkey in Hretained; rewrite Hretained; exact Hlookup. }
  assert (Habsent : current.(TskState).(parkedTaskStacks) (task_stack_key transfer.(os_int_exit_incoming_stack)) = None).
  { unfold current, os_int_exit_installed_state.
    cbn [replace_TskS replace_SchedS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup. }
  pose proof (task_retained_call_stack_merge external platform port abi current.(TskState) focus retained
    Hbinding Hfocus ltac:(rewrite Hlease; exact Hkey) Hslice
    ltac:(unfold task_stack_live_sp; rewrite Hused, Hlease; exact Hsp)
    ltac:(rewrite Hlease, Hfragments, Hkey; exact Hlookup')) as Hmerge.
  exists transfer, installed, selected, node; split; [exact Hstate|]. split; [exact Hinstall|].
  split; [exact Hinitial|].
  intros final Hrestore_run; destruct (Hrestore final Hrestore_run) as [Hexecution Hfinal].
  fold current in Hfinal, Hready, Hgen, Hcovered.
  fold current.
  assert (Hvalid : UCOS2_state_inv sg current).
  { match type of Hfinal with ?P final => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve final Hfinal)). }
  split; [exact Hexecution|]. split.
  - unfold current, os_int_exit_installed_state; rewrite Hstate.
    change (isRunning (os_sched_ready_checkpoint (os_int_exit_after_nesting state)) = true).
    unfold os_sched_ready_checkpoint.
    destruct (os_sched_selection_enabled (os_int_exit_after_nesting state));
      [destruct (os_sched_requests_switch (os_int_exit_after_nesting state))|]; exact Hrunning.
  - split; [exact Hnest|]. split; [exact Hlookup'|]. split; [exact Habsent|]. split.
    + intros saved_stack sp Hpointer.
      change (task_saved_pointer_at current saved_stack sp).
      unfold task_saved_pointer_at; rewrite Hused; exact Hpointer.
    + split.
      * intros invocation Hbefore; split; [exact Hvalid|].
        unfold current, os_int_exit_installed_state; rewrite Hstate.
        split; [reflexivity|]. split; [intros; assumption|reflexivity].
      * match type of Hfinal with ?P final => match goal with |- ?Q final => assert (Hclose : P |-- Q) end end.
        { eapply derivable1_trans with (y :=
            (armv7a_dormant_continuation abi retained ** armv7a_task_call_stacks abi current.(TskState) focus
              (task_stack_take current.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack))) **
            (armv7a_task_restored_execution external platform port abi selected ** UCOS2_inv sg current **
             unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
               handler.(os_int_exit_handler_fragments) ** frame)).
          - entailer!.
          - sep_apply_l_atomic Hmerge; unfold os_sched_source_selected_post; entailer!. }
        exact (Hclose final Hfinal).
Qed.

(** The selector's initial destination becomes an actual Create entry.
    The earlier pending call keeps its reservation, identity and saved SP;
    registration uses the selected frame's existing entry ABI. *)
Lemma task_create_irq_initial_entry_source : forall environment
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (entry_abi : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg args name state focus fragments handler before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let lease := focus.(armv7a_focus_call).(os_sched_call_stack) in
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true -> state.(SchedState).(readyList) <> [] ->
  (forall slot node, (os_int_exit_ready_checkpoint true state).(SchedState).(highRdyTid) = Some slot ->
    state.(TskState).(inUsedTaskStates) slot = Some node -> (slot, node.(taskGeneration)) <> task_stack_key lease) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true state) (os_int_exit_ready_checkpoint true state) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  (kernel_client_call_stack_world abi sg focus (lease.(stackLeaseRegion), fragments) state **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) before ->
  exists prepared,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    (forall hooked, kernel_heap_execution [] prepared hooked ->
      exists transfer installed selected,
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        (forall final,
          selected.(armv7a_continuation_call) = None ->
          task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
            0 selected.(armv7a_continuation_fragments) ->
          armv7a_restore_transition abi handler selected installed final ->
          let current := os_int_exit_installed_state transfer in
          let call := armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
            selected.(armv7a_continuation_fragments) in
          let registered := armv7a_initial_call_registered selected current in
          os_int_exit_source_selected_execution environment.(task_stack_call_external)
            environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
            sg state handler transfer selected before final /\
          task_create_source_entry sg args name call registered /\
          task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call) /\
          registered.(IntrState).(intNesting) = 0 /\
          registered.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) =
            Some (lease.(stackLeaseRegion), fragments) /\
          (forall saved_stack sp, task_saved_pointer_at state saved_stack sp ->
            task_saved_pointer_at registered saved_stack sp) /\
          (forall invocation, task_tcb_init_call_preserved sg invocation state registered) /\
          (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
             call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
           kernel_program_inv sg registered ** armv7a_task_call_stacks abi registered.(TskState) focus
             registered.(TskState).(parkedTaskStacks) **
           (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
             handler.(os_int_exit_handler_fragments) ** frame)) final)).
Proof.
  intros environment task_abi initial entry_abi sg args name state focus fragments handler before frame abi lease
    Hrunning Hswitch Hnonempty Hdifferent Haddress Hhook Hname Hpre.
  destruct (task_irq_foreign_selected_source _ _ _ abi task_abi initial sg state focus fragments handler
    before frame Hrunning Hswitch Hnonempty Hdifferent Haddress Hhook Hpre) as [prepared [Hprefix Hselect]].
  exists prepared; split; [exact Hprefix|]. intros hooked Hempty.
  destruct (Hselect hooked Hempty) as [transfer [installed [selected [node [Hstate [Hinstall [Hinitial Hreturn]]]]]]].
  exists transfer, installed, selected; split; [exact Hinstall|].
  intros final Hnone Hgeometry Hrestore current call registered.
  destruct (Hreturn final Hrestore) as [Hexecution [Hcurrent_running [Hzero [Hfocus [Habsent
    [Hpointer [Hpreserved Howned]]]]]]].
  assert (Hcurrent_name : task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) current).
  { unfold current, os_int_exit_installed_state; rewrite Hstate; exact Hname. }
  match type of Howned with ?P final => assert (Hregister : P |--
    coq_prop (task_create_source_entry sg args name call registered /\
      task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
       call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) ** kernel_program_inv sg registered **
     armv7a_task_call_stacks abi registered.(TskState) focus registered.(TskState).(parkedTaskStacks) **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))) end.
  { eapply derivable1_trans with (y :=
      (os_sched_source_selected_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
        environment.(task_stack_call_port) abi sg focus transfer.(os_int_exit_incoming_stack) selected node current **
       unmap_table_rep sg) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)).
    - entailer!.
    - eapply derivable1_trans.
      + apply derivable1_sepcon_mono.
        * exact (task_create_selected_initial_entry_focused_world environment entry_abi sg args name focus
            transfer.(os_int_exit_incoming_stack) selected node current Hcurrent_running (Hinitial Hnone)
            Hnone Hgeometry Habsent Hcurrent_name).
        * reflexivity.
      + cbv zeta; entailer!. }
  destruct (Hregister final Howned) as [[Hentry Hcoverage] Hregistered].
  split; [exact Hexecution|]. split; [exact Hentry|]. split; [exact Hcoverage|].
  split; [exact Hzero|]. split; [exact Hfocus|]. split.
  - intros saved_stack sp Hsaved; exact (Hpointer saved_stack sp Hsaved).
  - split; [|exact Hregistered].
    intros invocation Hvalid.
    destruct (Hpreserved invocation Hvalid) as [Hcurrent_valid [Hcreation [Hactive Hnames]]].
    split; [exact (proj1 (proj1 Hentry))|]. split; [exact Hcreation|]. split; [|exact Hnames].
    intros origin Hbefore.
    apply task_begin_invocation_preserves_invocation_active.
    + pose proof (proj1 (proj2 Hcurrent_valid)) as Htasks; unfold task_in_range in Htasks; tauto.
    + exact (Hactive origin Hbefore).
Qed.
