Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_irq_sched_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** TCBInit's actual Restore can be interrupted before its BX. On the
    switch branch, the creator stays parked and the
    selected task starts/resumes. The theorem intentionally does not run
    the creator's Restore suffix on that other task. This source branch
    has no intervening handler work and uses the explicit no-write hook.
    The distinct selected key follows from the ready caller's current
    priority and the actual unequal-priority guard; it is not an extra
    premise. Other handler/source paths remain obligations of the public join. *)
Lemma task_create_tcb_restore_irq_switch_source : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg acquired released node handler suspended publication focus payload
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_create_call_stage call released ->
  armv7a_task_frame_slice suspended ->
  released.(SchedState).(isRunning) = true -> released.(IntrState).(intNesting) = 0 ->
  released.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  released.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened released.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  task_stack_live_coverage released.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  os_int_exit_requests_switch true parked = true ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true parked) (os_int_exit_ready_checkpoint true parked) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
   task_tcb_init_stack_context environment call ** kernel_program_inv sg released **
   armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
  (forall written irq_input saved_heap,
    armv7a_restore_prefix_transition restore cursor before written irq_input ->
    armv7a_save_transition abi handler suspended irq_input saved_heap ->
    exists registry_heap prepared,
      written = kernel_restore_write_cpsr cursor /\
      kernel_heap_writes (armv7a_continuation_save_writes suspended)
        irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
      kernel_heap_execution (armv7a_irq_live_entry_writes sg released
        call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
        saved_heap registry_heap /\
      os_int_exit_source_switch_prefix_execution sg registry_heap prepared /\
      (forall hooked, kernel_heap_execution [] prepared hooked ->
        exists transfer installed selected selected_node,
          transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true parked /\
          sched_install_heap_fragment sg hooked installed
            (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
            selected.(armv7a_continuation_sp) /\
          selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
          (task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
            armv7a_continuation_focus_binding focus selected) /\
          sched_current_ready_at (os_int_exit_installed_state transfer).(TskState)
            (os_int_exit_installed_state transfer).(SchedState)
            transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) selected_node /\
          selected_node.(taskGeneration) = transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
          task_stack_live_coverage (os_int_exit_installed_state transfer).(TskState)
            (Some (task_stack_key transfer.(os_int_exit_incoming_stack))) /\
          (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
            (task_stack_key suspended.(armv7a_continuation_stack)) =
            Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
              suspended.(armv7a_continuation_fragments)) /\
          (forall final, armv7a_restore_transition abi handler selected installed final ->
            os_int_exit_source_selected_execution environment.(task_stack_call_external)
              environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
              sg parked handler transfer selected registry_heap final /\
            (armv7a_task_restored_execution environment.(task_stack_call_external)
               environment.(task_stack_call_platform) environment.(task_stack_call_port) abi selected **
             task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
             (UCOS2_inv sg (os_int_exit_installed_state transfer) **
              armv7a_dormant_continuation abi suspended **
              armv7a_task_call_stacks abi (os_int_exit_installed_state transfer).(TskState) focus
                (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
                  suspended.(armv7a_continuation_stack)) ** (unmap_table_rep sg ** frame))) final))).
Proof.
  intros environment critical arch restore task_abi initial sg acquired released node handler suspended
    publication focus payload saved cursor before frame call abi parked Horigin Hstage Hslice Hrunning
    Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    Hswitch Hhook Hr0 Hmask Hhandler Hpre written irq_input saved_heap Hprefix Hsave.
  match type of Hpre with ?P before => assert (Hrelease : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_program_inv sg released **
     armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold task_tcb_init_stack_context; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region _ _ _ _ restore sg call saved acquired
    cursor before written irq_input _ Hr0 Hmask (Hrelease before Hpre) Hprefix)
    as [Hwritten [Hmemory Hreleased]].
  match type of Hreleased with ?P irq_input => assert (Hirq : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg released **
     armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
     (unmap_table_rep sg ** frame))) end.
  { unfold os_int_exit_frame_save_pre; rewrite Hhandler, kernel_program_inv_split_unmap; entailer!. }
  assert (Hready : task_create_irq_caller_stage call released).
  { eapply task_create_call_stage_irq_entry; eassumption. }
  assert (Hready_parked : task_create_irq_caller_stage call parked).
  { eapply task_create_irq_deposit_preserves_caller_stage; eassumption. }
  assert (Hnonempty : parked.(SchedState).(readyList) <> []).
  { destruct Hready_parked as [_ [ready [Hlookup [Hcurrent_ready [Hgeneration Hready_if]]]]].
    pose proof (proj1 (os_int_exit_requests_switch_iff true parked) Hswitch) as [_ [Hschedule _]].
    pose proof (proj2 (proj2 (proj1 (interrupt_exit_requests_schedule_iff true parked.(IntrState)) Hschedule)))
      as Hlock.
    destruct (Hready_if Hlock) as [_ [_ [_ [Hin _]]]].
    intro Hnil; rewrite Hnil in Hin; contradiction. }
  destruct (armv7a_irq_source_save_preserves_pending_call _ _ _ abi sg released node handler suspended
    publication focus payload (unmap_table_rep sg ** frame) irq_input saved_heap
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus (Haddress _) Hregion Hgeometry
    Hpublication Hsp Hcoverage (Hirq irq_input Hreleased) Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered [Hretained [Hjoint Hmerged]]]]]].
  match type of Hjoint with ?P registry_heap => assert (Horder : P |--
    UCOS2_inv sg parked ** unmap_table_rep sg **
    (armv7a_dormant_continuation abi suspended **
     armv7a_task_call_stacks abi parked.(TskState) focus
       (task_stack_take parked.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_stack)) **
     (interrupt_platform_running environment.(task_stack_call_platform)
        handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame))) by entailer!
  end.
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hentry [Hcall [Hbinding Hobserved]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hvalid_parked : UCOS2_state_inv sg parked).
  { match type of Hjoint with ?P registry_heap => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hjoint)). }
  assert (Hdifferent : forall slot selected_node,
    (os_int_exit_ready_checkpoint true parked).(SchedState).(highRdyTid) = Some slot ->
    parked.(TskState).(inUsedTaskStates) slot = Some selected_node ->
    (slot, selected_node.(taskGeneration)) <> task_stack_key suspended.(armv7a_continuation_stack)).
  { intros slot selected_node Hselected Hselected_node Hkey.
    rewrite Hlease in Hkey; unfold task_stack_key in Hkey.
    assert (Hslot : slot = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst slot.
    destruct (proj2 Hready_parked) as [caller
      [Hcaller [Hcaller_current [Hcaller_generation Hready_if]]]].
    pose proof (proj1 (os_int_exit_requests_switch_iff true parked) Hswitch) as [_ [Hschedule _]].
    pose proof (proj2 (proj2 (proj1 (interrupt_exit_requests_schedule_iff true parked.(IntrState)) Hschedule)))
      as Hlock.
    destruct (Hready_if Hlock) as [_ [_ [Hcaller_priority [Hin Heffective]]]].
    assert (selected_node = caller) by congruence; subst selected_node.
    destruct (proj1 (os_sched_requests_switch_iff (os_int_exit_after_nesting parked)) Hswitch)
      as [Hselection Hunequal].
    assert (Hhigh : (os_int_exit_ready_checkpoint true parked).(SchedState).(highRdyTid) =
      hd_error parked.(SchedState).(readyList)).
    { unfold os_int_exit_ready_checkpoint; cbn [replace_SchedS SchedState].
      unfold os_sched_ready_checkpoint; rewrite Hselection.
      destruct (os_sched_requests_switch (os_int_exit_after_nesting parked)); reflexivity. }
    rewrite Hhigh in Hselected.
    destruct parked.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    cbn [hd_error] in Hselected; injection Hselected as Hhead; subst head.
    assert (Hsg : valid_stable_glob_vars sg).
    { pose proof (proj1 Hvalid_parked) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
    change (sched_selected_priority parked.(TskState) parked.(SchedState) <>
      sched_priority_byte parked.(SchedState).(curSchedPrio)) in Hunequal.
    rewrite (sched_selected_priority_eq_head sg _ _ _ _ _ Hsg
      (proj1 (proj1 (proj2 (proj2 Hvalid_parked)))) Hlist Hcaller), Hcaller_priority in Hunequal.
    apply Hunequal; reflexivity. }
  destruct (armv7a_irq_switch_source_preserves_pending_split _ _ _ abi task_abi initial sg parked
    suspended focus handler frame registry_heap (proj1 Hready_parked) Hswitch Hnonempty Hdifferent Haddress
    Hcovered Hhook (Horder registry_heap Hjoint)) as [prepared [Hexit Hcontinue]].
  assert (Hparked : parked.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state; rewrite Hlease.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_park_fragments_lookup. }
  exists registry_heap, prepared.
  split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|]. split; [exact Hexit|].
  intros hooked Hhook_run.
  destruct (Hcontinue hooked Hhook_run) as [transfer [installed [selected [selected_node
    [Hstate [Hdestination [Hinstall [Hselected [Hfocused [Hready_selected
      [Hgeneration [Hcoverage_selected [Hkept Hrestore_selected]]]]]]]]]]]]].
  exists transfer, installed, selected, selected_node.
  split; [exact Hstate|]. split; [exact Hinstall|]. split; [exact Hselected|].
  split; [exact Hfocused|]. split; [exact Hready_selected|]. split; [exact Hgeneration|].
  split; [exact Hcoverage_selected|]. split; [rewrite Hkept; exact Hparked|exact Hrestore_selected].
Qed.

