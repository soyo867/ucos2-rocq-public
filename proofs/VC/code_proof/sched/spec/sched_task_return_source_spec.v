Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition os_sched_task_current_ready (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  exists node,
    sched_current_ready_at state.(TskState) state.(SchedState)
      call.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration).

Lemma os_sched_prefix_current_ready_iff : forall call state,
  os_sched_task_current_ready call (os_sched_prefix_state state) <->
  os_sched_task_current_ready call state.
Proof.
  intros call state; unfold os_sched_task_current_ready, sched_current_ready_at,
    os_sched_prefix_state; cbn [replace_SchedS TskState SchedState].
  destruct (os_sched_ready_checkpoint_frame state) as [Hr [Hc [Hp Hi]]].
  rewrite Hr, Hc, Hp; reflexivity.
Qed.

Lemma os_sched_save_sp_preserves_task_ready : forall call state sp,
  os_sched_task_current_ready call state ->
  os_sched_task_current_ready call
    (os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot) sp).
Proof.
  intros call state sp [node [[Hnode Hrest] Hgeneration]].
  unfold os_sched_save_current_sp; rewrite Hnode.
  exists (task_set_saved_sp node sp); split; [|exact Hgeneration].
  unfold sched_current_ready_at; cbn [replace_TskS TskState SchedState glob_task_set_usedtask inUsedTaskStates].
  rewrite Z.eqb_refl; split; [reflexivity|exact Hrest].
Qed.

Lemma os_sched_irq_install_selected_ready : forall external sg transfer,
  UCOS2_state_inv sg transfer.(os_int_exit_hooked_state) ->
  sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
    transfer.(os_int_exit_hooked_state).(SchedState) ->
  os_int_exit_destination_binding external transfer ->
  exists node,
    sched_current_ready_at (os_int_exit_installed_state transfer).(TskState)
      (os_int_exit_installed_state transfer).(SchedState)
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration).
Proof.
  intros external sg transfer Hvalid Hhigh
    [Hselected [[node [Hnode [Hgeneration [Hpriority Hsp]]]] Hrest]].
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hready.
  unfold sched_high_ready_consistency in Hhigh.
  destruct transfer.(os_int_exit_hooked_state).(SchedState).(readyList) as [|slot tail] eqn:Hlist.
  - destruct Hhigh as [Hnone Hnone_priority]; congruence.
  - destruct Hhigh as [Hhead Hhead_node].
    assert (Hslot : slot = transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) by congruence.
    destruct (Hready transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) (or_introl Hslot))
      as [ready_node [Hready_node [Hrange Heffective]]].
    assert (ready_node = node) by congruence; subst ready_node.
    assert (Hin : In transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_hooked_state).(SchedState).(readyList)).
    { rewrite Hlist; left; exact Hslot. }
    exists node; split; [|exact Hgeneration].
    unfold sched_current_ready_at.
    change (transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates)
        transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) = Some node /\
      transfer.(os_int_exit_hooked_state).(SchedState).(highRdyTid) =
        Some transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) /\
      transfer.(os_int_exit_hooked_state).(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
        transfer.(os_int_exit_hooked_state).(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true).
    exact (conj Hnode (conj Hselected (conj Hpriority (conj Hin Heffective)))).
Qed.

(** These observations are produced by the actual final no-switch or
    selected-install source.  No constructor assumes current-ready, and no
    constructor transports it across an arbitrary client/ISR interval. *)
Inductive os_sched_task_ready_source (environment : TaskStackCallEnvironment) sg :
  OsSchedCallContext -> UCOS2_Verify_State -> Prop :=
| OsSchedTaskReadyNonswitch : forall call state,
    UCOS2_state_inv sg state -> kernel_call_task_source call state ->
    sched_current_consistency state.(TskState) state.(SchedState) ->
    os_sched_selection_enabled state = true -> os_sched_requests_switch state = false ->
    state.(SchedState).(readyList) <> [] ->
    os_sched_task_ready_source environment sg call state
| OsSchedTaskReadySelected : forall context outgoing hooked incoming resumed returned,
    UCOS2_state_inv sg hooked ->
    sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
    os_sched_destination_binding environment.(task_stack_call_external)
      context outgoing hooked incoming resumed ->
    returned.(os_sched_call_stack) = incoming ->
    os_sched_task_ready_source environment sg returned
      (os_sched_install_context context outgoing incoming hooked)
| OsSchedTaskReadyInterruptSelected : forall transfer returned,
    UCOS2_state_inv sg transfer.(os_int_exit_hooked_state) ->
    sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
      transfer.(os_int_exit_hooked_state).(SchedState) ->
    os_int_exit_destination_binding environment.(task_stack_call_external) transfer ->
    returned.(os_sched_call_stack) = transfer.(os_int_exit_incoming_stack) ->
    os_sched_task_ready_source environment sg returned (os_int_exit_installed_state transfer)
| OsSchedTaskReadyTake : forall call state lease,
    os_sched_task_ready_source environment sg call state ->
    os_sched_task_ready_source environment sg call (os_int_exit_wrapper_restored_state state lease)
| OsSchedTaskReadySaveSP : forall call state sp,
    os_sched_task_ready_source environment sg call state ->
    os_sched_task_ready_source environment sg call
      (os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot) sp)
| OsSchedTaskReadyPrefix : forall call state,
    os_sched_task_ready_source environment sg call state ->
    os_sched_task_ready_source environment sg call (os_sched_prefix_state state).

Lemma os_sched_task_ready_source_current_ready : forall environment sg call state,
  os_sched_task_ready_source environment sg call state -> os_sched_task_current_ready call state.
Proof.
  intros environment sg call state Hsource; induction Hsource.
  - apply (proj1 (os_sched_prefix_current_ready_iff call state)).
    eapply os_sched_nonswitch_current_ready_at; eassumption.
  - destruct (task_create_install_selected_ready environment.(task_stack_call_external) sg
      context outgoing hooked incoming resumed H H0 H1) as [node [Hready Hgeneration]].
    exists node; rewrite H2; auto.
  - destruct (os_sched_irq_install_selected_ready environment.(task_stack_call_external) sg transfer
      H H0 H1) as [node [Hready Hgeneration]].
    exists node; rewrite H2; auto.
  - exact IHHsource.
  - apply os_sched_save_sp_preserves_task_ready; exact IHHsource.
  - apply (proj2 (os_sched_prefix_current_ready_iff call state)); exact IHHsource.
Qed.

Lemma os_sched_task_ready_source_current_consistency : forall environment sg call state,
  os_sched_task_ready_source environment sg call state ->
  sched_current_consistency state.(TskState) state.(SchedState).
Proof.
  intros environment sg call state Hsource.
  destruct (os_sched_task_ready_source_current_ready environment sg call state Hsource)
    as [node [[Hnode [Hcurrent [Hcache Hrest]]] Hgeneration]].
  unfold sched_current_consistency; rewrite Hcurrent; exists node; auto.
Qed.

Lemma os_sched_task_irq_same_priority_state_eq : forall entry,
  interrupt_exit_requests_schedule true entry.(IntrState) = true ->
  sched_selected_priority entry.(TskState) entry.(SchedState) =
    sched_priority_byte entry.(SchedState).(curSchedPrio) ->
  os_int_exit_same_priority_state entry = os_sched_prefix_state (os_int_exit_after_nesting entry).
Proof.
  intros entry Henabled Hequal.
  assert (Hselection : os_sched_selection_enabled (os_int_exit_after_nesting entry) = true).
  { rewrite os_int_exit_after_nesting_selection_eq; exact Henabled. }
  assert (Hnoswitch : os_sched_requests_switch (os_int_exit_after_nesting entry) = false).
  { unfold os_sched_requests_switch; rewrite Hselection.
    cbn [os_int_exit_after_nesting replace_IntrS TskState SchedState];
      unfold sched_switch_byte_guard; rewrite Hequal, Z.eqb_refl; reflexivity. }
  unfold os_int_exit_same_priority_state, os_int_exit_selection_state,
    os_sched_prefix_state, os_sched_ready_checkpoint.
  rewrite Hselection, Hnoswitch; reflexivity.
Qed.

Lemma os_sched_task_irq_same_priority_enabled : forall entry lease,
  interrupt_exit_requests_schedule true entry.(IntrState) = true ->
  sched_selected_priority entry.(TskState) entry.(SchedState) =
    sched_priority_byte entry.(SchedState).(curSchedPrio) ->
  os_sched_selection_enabled
    (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state entry) lease) = true.
Proof.
  intros entry lease Henabled Hequal.
  rewrite (os_sched_task_irq_same_priority_state_eq entry Henabled Hequal).
  change (os_sched_selection_enabled (os_int_exit_after_nesting entry) = true).
  rewrite os_int_exit_after_nesting_selection_eq; exact Henabled.
Qed.

(** OSIntExit's same-priority return performs the real decrement and fresh
    selector before the wrapper take.  Its current consistency may come
    from a priority-changing ISR; no old priority value is transported. *)
Lemma os_sched_task_irq_same_priority_ready_source : forall environment sg call entry lease,
  UCOS2_state_inv sg entry -> kernel_call_task_source call entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  interrupt_exit_requests_schedule true entry.(IntrState) = true ->
  sched_selected_priority entry.(TskState) entry.(SchedState) =
    sched_priority_byte entry.(SchedState).(curSchedPrio) ->
  entry.(SchedState).(readyList) <> [] ->
  os_sched_task_ready_source environment sg call
    (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state entry) lease).
Proof.
  intros environment sg call entry lease Hvalid Hsource Hcurrent Henabled Hequal Hnonempty.
  assert (Hselection : os_sched_selection_enabled (os_int_exit_after_nesting entry) = true).
  { rewrite os_int_exit_after_nesting_selection_eq; exact Henabled. }
  assert (Hnoswitch : os_sched_requests_switch (os_int_exit_after_nesting entry) = false).
  { unfold os_sched_requests_switch; rewrite Hselection.
    cbn [os_int_exit_after_nesting replace_IntrS TskState SchedState];
      unfold sched_switch_byte_guard; rewrite Hequal, Z.eqb_refl; reflexivity. }
  assert (Hstate : os_int_exit_same_priority_state entry = os_sched_prefix_state (os_int_exit_after_nesting entry)).
  { unfold os_int_exit_same_priority_state, os_int_exit_selection_state,
      os_sched_prefix_state, os_sched_ready_checkpoint.
    rewrite Hselection, Hnoswitch; reflexivity. }
  apply OsSchedTaskReadyTake; rewrite Hstate; apply OsSchedTaskReadyPrefix.
  eapply OsSchedTaskReadyNonswitch.
  - apply os_int_exit_after_nesting_preserves_validity; exact Hvalid.
  - exact Hsource.
  - exact Hcurrent.
  - exact Hselection.
  - exact Hnoswitch.
  - exact Hnonempty.
Qed.

(** Consume the real IRQ take/restore on the same field-owned heap.  The
    last selector source may be no-switch or selected; arbitrary clients
    cannot insert an unproved ready-preserving edge into this suffix. *)
Lemma os_sched_task_irq_fields_ready_return_source : forall environment sg state local suspended call node handler
  (interrupted_local frame : Assertion) before after,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  os_sched_task_ready_source environment sg (armv7a_continuation_resumed_call suspended call) state ->
  (UCOS2_fields_inv sg state ** store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState)
      (kernel_irq_fields_local local suspended interrupted_local)) state.(TskState).(parkedTaskStacks) **
    (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) before ->
  armv7a_restore_transition environment.(task_stack_call_continuations) handler suspended before after ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  os_sched_task_ready_source environment sg (armv7a_continuation_resumed_call suspended call) restored /\
  os_sched_task_current_ready (armv7a_continuation_resumed_call suspended call) restored /\
  (flag_source_save_input environment.(task_stack_call_continuations) (fun sg state => UCOS2_fields_inv sg state) local sg
    (Some (task_stack_key suspended.(armv7a_continuation_stack)))
    (armv7a_continuation_resumed_call suspended call)
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) restored interrupted_local **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros environment sg state local suspended call node handler interrupted_local frame before after
    Hcall Hcurrent Hnode Hgeneration Hparked Haddress Hcoverage Hready Hpre Hrestore restored.
  destruct (kernel_irq_restore_fields_local_resources environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg state local suspended call node handler interrupted_local frame
    before after Hcall Hcurrent Hnode Hgeneration Hparked Haddress Hcoverage Hpre Hrestore)
    as [Hmemory [Habsent Howned]].
  assert (Hcut : os_sched_task_ready_source environment sg
      (armv7a_continuation_resumed_call suspended call) restored) by (constructor; exact Hready).
  exact (conj Hmemory (conj Hcut (conj (os_sched_task_ready_source_current_ready _ _ _ _ Hcut) Howned))).
Qed.

Lemma os_sched_prefix_normal_return : forall call state,
  kernel_call_normal_return call state call (os_sched_prefix_state state).
Proof.
  intros; split; [unfold task_tcb_init_stack_same_call; auto|].
  unfold kernel_call_stack_available; destruct call.(os_sched_call_origin); auto.
Qed.

Lemma os_sched_prefix_control_rely : forall sg state,
  kernel_call_control_rely sg state (os_sched_prefix_state state).
Proof.
  intros; split; [|reflexivity].
  exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame state)))).
Qed.

(** The ready conclusion is joined to the SAME prefix/Restore heap produced
    by the checked fields source theorem.  Its input permits a blocked
    caller.  Restore transitions are the already selected platform boundary. *)
Lemma os_sched_task_nonswitch_return_source : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  local sg active call saved acquired state before (current_local frame : Assertion),
  UCOS2_state_inv sg state -> kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  os_sched_selection_enabled state = true -> os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  (flag_source_restore_input environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sg active call saved acquired state current_local ** frame) before ->
  exists prefix_heap,
    os_sched_modular_prefix_execution sg state before prefix_heap /\
    forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      os_sched_task_ready_source environment sg call (os_sched_prefix_state state) /\
      kernel_call_normal_return call state call (os_sched_prefix_state state) /\
      kernel_call_control_rely sg state (os_sched_prefix_state state) /\
      os_sched_c_return environment.(task_stack_call_external) critical sg state call call
        (os_sched_prefix_state state) /\
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (flag_source_save_input environment.(task_stack_call_continuations) kernel_program_fields_inv local sg
        active call (armv7a_irq_fiq_mask saved) (os_sched_prefix_state state) current_local ** frame) after.
Proof.
  intros environment critical arch restore local sg active call saved acquired state before current_local frame
    Hvalid Hsource Hcurrent Henabled Hnoswitch Hnonempty Hpre.
  destruct (flag_fields_source_sched_nonswitch_return_resources environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) critical arch
    environment.(task_stack_call_continuations) restore local sg active call saved acquired state before
    current_local frame Hnoswitch ltac:(auto) Hpre) as [prefix_heap [Hprefix Hreturn]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix.
  split.
  - apply OsSchedTaskReadyPrefix; eapply OsSchedTaskReadyNonswitch; eassumption.
  - split; [apply os_sched_prefix_normal_return|].
    split; [apply os_sched_prefix_control_rely|].
    exact (Hreturn cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix).
Qed.

(** The OSCtxSw return is before CPU Restore.  This producer opens the
    existing selected local exactly there and reconstructs the masked world;
    it does not substitute the later closed world for this call boundary. *)
Lemma os_sched_task_selected_masked_return_source : forall environment critical
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg context outgoing hooked original saved acquired receipt other resumed before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      task_tcb_init_stack_same_call returned original /\
      kernel_call_task_source returned current /\
      os_sched_task_ready_source environment sg returned current /\
      kernel_call_normal_return original hooked returned current /\
      kernel_call_control_rely sg hooked current /\
      environment.(task_stack_call_external).(os_sched_arch_resume_source) original returned /\
      (kernel_continuation_call_masked abi kernel_program_fields_inv other critical sg
        (task_stack_call_active_key returned) returned saved acquired current ** receipt ** frame) restored).
Proof.
  intros environment critical task_abi sg context outgoing hooked original saved acquired receipt other resumed before
    frame abi local resource current Hvalid Hhigh Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (kernel_saved_continuation_fields_install_source environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi sg context outgoing hooked
    original.(os_sched_call_stack) resumed local before frame Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold current in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hmemory [Harch Howned]].
  assert (Hlocal : local selected = kernel_sched_saved_local environment.(task_stack_call_platform) critical sg
      hooked.(TskState) original saved acquired selected ** receipt).
  { unfold local; apply kernel_sched_saved_local_resource_at_selected; exact Hlease. }
  rewrite Hlocal in Howned.
  assert (Hfacts : selected.(armv7a_continuation_call) = Some original /\
      armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
      original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
        original.(os_sched_call_stack).(stackLeaseGeneration) /\
      task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { match type of Howned with ?P restored => assert (Hexpose : P |-- coq_prop
      (selected.(armv7a_continuation_call) = Some original /\
       armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
       original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
         original.(os_sched_call_stack).(stackLeaseGeneration) /\
       task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin)) && TT) end.
    { unfold kernel_sched_saved_local; entailer!; intros heap Hheap; unfold coq_prop in *; tauto. }
    exact (proj1 (Hexpose restored Howned)). }
  destruct Hfacts as [Hcall [Hmask [Horigin Hactive]]].
  assert (Hreturned : returned = armv7a_continuation_resumed_call selected original).
  { unfold returned, kernel_selected_call; rewrite Hcall; reflexivity. }
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { rewrite Hreturned; unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hsource : kernel_call_task_source returned current).
  { unfold returned; eapply kernel_selected_saved_call_source.
    - exact Hbinding.
    - exact Hcall.
    - exact Horigin.
    - exact Hactive.
    - rewrite Hlease; exact Hcurrent. }
  assert (Hready : os_sched_task_ready_source environment sg returned current).
  { unfold current; eapply OsSchedTaskReadySelected; try eassumption; exact (proj2 (proj2 Hsame)). }
  assert (Hnormal : kernel_call_normal_return original hooked returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 Hsource), (proj2 (proj2 Hsame)); apply task_stack_take_lookup. }
  assert (Habsent : current.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None)
    by apply task_stack_take_lookup.
  assert (Hunfocus : store_parked_continuations
      (kernel_saved_continuation_entry abi current.(TskState) local) current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) other)
      current.(TskState).(parkedTaskStacks)).
  { unfold local; apply kernel_saved_continuation_resource_map_unfocus_absent; exact Habsent. }
  split; [exact Hcall|]. split; [exact Hsame|]. split; [exact Hsource|]. split; [exact Hready|].
  split; [exact Hnormal|]. split; [split; reflexivity|].
  split.
  { unfold armv7a_task_restored_source in Harch; rewrite Hcall in Harch; rewrite Hreturned; exact Harch. }
  match type of Howned with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic Hunfocus.
    assert (Hkey : task_stack_call_active_key returned = Some (task_stack_key original.(os_sched_call_stack))).
    { rewrite Hreturned; unfold task_stack_call_active_key, armv7a_continuation_resumed_call; cbn; rewrite Horigin; reflexivity. }
    rewrite Hkey.
    unfold kernel_continuation_call_masked, kernel_continuation_inv, armv7a_task_restored_execution.
    rewrite Hcall, Hmask, Hreturned.
    unfold kernel_sched_saved_local, kernel_call_execution_owned, critical_region_masked,
      armv7a_continuation_resumed_call; cbn [os_sched_call_invocation os_sched_call_origin]; entailer!. }
  exact (Hclose restored Howned).
Qed.

(** Retain the selected descriptor, real install heap and returned receipt
    from the existing source producer.  Ready and normal-return are derived
    from that selected key and its actual take, never supplied as premises. *)
Lemma os_sched_task_selected_receipt_return_source :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg context outgoing hooked source_tasks original saved acquired receipt other resumed before
    (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    source_tasks original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      task_tcb_init_stack_same_call returned original /\
      kernel_call_task_source returned current /\
      os_sched_task_ready_source environment sg returned current /\
      kernel_call_normal_return original hooked returned current /\
      kernel_call_control_rely sg hooked current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        (kernel_continuation_call_closed abi kernel_program_fields_inv other sg
           (Some (task_stack_key original.(os_sched_call_stack))) returned
           (armv7a_irq_fiq_mask saved) current ** receipt ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked source_tasks original saved acquired
    receipt other resumed before frame abi local resource current Hvalid Hhigh Hactive Hsaved Hdestination
    Haddress Hcoverage Hpre.
  destruct (os_sched_fields_modular_saved_call_receipt_return environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) critical arch abi task_abi restore
    sg context outgoing hooked source_tasks original saved acquired receipt other resumed before frame
    Hactive Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease Hreturn]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hreturn restored Htask_restore) as [Hcall [Hi [Ho [Hs [Hsource Htail]]]]].
  fold current returned in Hi, Ho, Hs, Hsource, Htail.
  assert (Hsame : task_tcb_init_stack_same_call returned original)
    by (unfold task_tcb_init_stack_same_call; auto).
  assert (Hnormal : kernel_call_normal_return original hooked returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available.
    pose proof (proj1 Hsource) as Horigin; rewrite Horigin, Hs.
    apply task_stack_take_lookup. }
  split; [exact Hcall|]. split; [exact Hsame|]. split; [exact Hsource|].
  split.
  - unfold current; eapply OsSchedTaskReadySelected; eassumption.
  - split; [exact Hnormal|]. split; [split; reflexivity|exact Htail].
Qed.
