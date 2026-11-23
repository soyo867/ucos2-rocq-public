Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_irq_return_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_world_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_pending_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_focused_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Return to an earlier task from a handler that interrupted a DIFFERENT
    running task. The registry has already produced its current all-parked
    world and original-call registration. This consumer executes the real
    OSIntExit counter/selector and cache installation before taking the
    focused frame, then the IRQ restore and the original OS_Sched Restore.
    The high-ready equality is the actual return branch, not a replacement
    for the selector execution or a promise that every IRQ returns here. *)
Lemma task_create_sched_selected_irq_return_post : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state handler original suspended saved acquired call_before
  region args task_return lower old_frame upper before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let checkpoint := os_int_exit_ready_checkpoint true state in
  let cached := replace_SchedS (sched_install_selected checkpoint.(SchedState)) checkpoint in
  let current := os_int_exit_wrapper_restored_state cached original.(os_sched_call_stack) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  checkpoint.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg checkpoint checkpoint ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_client_call_stack_world abi sg focus payload state **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame))) before ->
  exists prepared installed selected,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    kernel_heap_execution [] prepared prepared /\
    kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg checkpoint checkpoint /\
    sched_install_heap_fragment sg prepared installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    task_invocation_active checkpoint.(TskState) original.(os_sched_call_invocation)
      original.(os_sched_call_origin) /\
    (forall irq_return cursor written middle final_cursor after,
      armv7a_restore_transition abi handler selected installed irq_return ->
      cursor.(kernel_restore_r0) = saved ->
      cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      armv7a_restore_prefix_transition restore cursor irq_return written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
      kernel_call_task_source (armv7a_continuation_resumed_call selected original) current /\
      (os_sched_stack_return_post environment kernel_program_inv sg original
         (armv7a_irq_fiq_mask saved) call_before **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) after /\
      (task_create_stack_post environment critical sg region args task_return lower old_frame upper
         original (armv7a_irq_fiq_mask saved) 0 **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) after).
Proof.
  intros environment critical arch restore sg state handler original suspended saved acquired call_before
    region args task_return lower old_frame upper before frame abi focus payload checkpoint cached current
    Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre.
  match type of Hpre with ?P before => assert (Hinput : P |--
    kernel_client_call_stack_world abi sg focus payload state **
    (interrupt_platform_running environment.(task_stack_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
      (emp ** frame)))) by entailer! end.
  destruct (sched_selected_irq_return_resources environment critical arch restore (fun _ _ => emp)
    sg state handler original suspended saved acquired before frame
    ltac:(reflexivity) Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hrunning
    Hswitch Hnonempty Hhigh Hhook Haddress (Hinput before Hpre))
    as [prepared [installed [selected [Hprefix [Hempty [Hhooked [Hinstall
      [Hcpsr [Hregisters [Hsame [Hactive_now [Hready_now Hreturn]]]]]]]]]]]].
  exists prepared, installed, selected.
  split; [exact Hprefix|]. split; [exact Hempty|]. split; [exact Hhooked|].
  split; [exact Hinstall|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  split; [exact Hactive_now|].
  intros irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix.
  destruct (Hreturn irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix)
    as [Hexecution [Hordinary Howned]].
  assert (Hminimal : (os_sched_stack_return_post environment kernel_program_inv sg original
    (armv7a_irq_fiq_mask saved) call_before **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) after).
  { match type of Howned with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
    { unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post.
      Exists (armv7a_continuation_resumed_call selected original) current.
      unfold kernel_stack_call_closed, kernel_stack_inv; entailer!. }
    exact (Hpost after Howned). }
  split; [exact Hexecution|]. split; [exact Hordinary|]. split; [exact Hminimal|].
  match type of Hminimal with ?P after => match goal with |- ?Q after => assert (Hpublic : P |-- Q) end end.
  { sep_apply_l_atomic (os_sched_stack_return_post_returns_create environment critical sg original
      original (armv7a_irq_fiq_mask saved) call_before region args task_return lower old_frame upper
      ltac:(unfold task_tcb_init_stack_same_call; auto)); entailer!. }
  exact (Hpublic after Hminimal).
Qed.

(** First selected INITIAL entry -> its actual foreign IRQ save/deposit ->
    the SAME registered heap/state/source trace -> actual selection of the
    original pending task -> IRQ restore -> original final MSR/BX.

    The first state is exactly the earlier SP-store/install producer's
    state. Pending presence, saved SP and the foreign key's absence are
    established here from that state and the selected frame; none is a new
    public API premise. Initial-call registration preserves the already
    active original invocation using the existing generation closure.
    This is the explicit initial-destination, one-IRQ, no-write-hook return
    branch. Other destinations and non-returning traces remain distinct. *)
Lemma task_create_selected_foreign_irq_return_post : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (initial : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  extra_resources extra_step extra_effect sg checkpoint original_node original suspended incoming
  first_selected first_node child_args child_name handler foreign_saved publication
  saved acquired call_before region args task_return lower old_frame upper
  before saved_heap (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let first_state := os_sched_install_context original suspended.(armv7a_continuation_fragments)
    incoming updated in
  let foreign := armv7a_initial_call first_selected first_state.(TskState).(taskLifecycle).(taskNextInvocation)
    first_selected.(armv7a_continuation_fragments) in
  let entry := armv7a_initial_call_registered first_selected first_state in
  let parked := armv7a_irq_live_parked_state entry foreign foreign_saved.(armv7a_continuation_sp)
    foreign_saved.(armv7a_continuation_fragments) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  checkpoint.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some original_node ->
  original_node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active first_state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  first_state.(SchedState).(isRunning) = true ->
  first_state.(IntrState).(intNesting) = 0 ->
  armv7a_initial_frame_binding first_selected ->
  first_selected.(armv7a_continuation_call) = None ->
  task_stack_fragments_in_range first_selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0
    first_selected.(armv7a_continuation_fragments) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args child_args child_name) first_state ->
  handler.(os_int_exit_interrupted_call) = foreign ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask first_selected.(armv7a_continuation_cpsr) ->
  armv7a_task_frame_slice foreign_saved ->
  valid_task_stack_region foreign.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range foreign.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    foreign_saved.(armv7a_continuation_fragments) ->
  task_publication_happened first_state.(TskState) publication
    foreign.(os_sched_call_stack).(stackLeaseSlot) foreign.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range foreign.(os_sched_call_stack).(stackLeaseRegion)
    foreign_saved.(armv7a_continuation_sp) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None extra_effect ->
  (os_sched_source_selected_post environment.(task_stack_call_external)
     environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
     sg focus incoming first_selected first_node first_state **
   unmap_table_rep sg **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    frame)) before ->
  armv7a_save_transition abi handler foreign_saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes foreign_saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      foreign.(os_sched_call_stack).(stackLeaseSlot) foreign_saved.(armv7a_continuation_sp))
      saved_heap registry_heap /\
    (forall closed_heap,
      kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
        KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
          KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          original.(os_sched_call_invocation) None original.(os_sched_call_origin)
          parked stopped returned_origin returned /\
        (stopped = false ->
         returned.(SchedState).(isRunning) = true ->
         os_int_exit_requests_switch true returned = true ->
         returned.(SchedState).(readyList) <> [] ->
         (os_int_exit_ready_checkpoint true returned).(SchedState).(highRdyTid) =
           Some original.(os_sched_call_stack).(stackLeaseSlot) ->
         kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg
           (os_int_exit_ready_checkpoint true returned) (os_int_exit_ready_checkpoint true returned) ->
         exists prepared installed selected,
           os_int_exit_source_switch_prefix_execution sg closed_heap prepared /\
           kernel_heap_execution [] prepared prepared /\
           sched_install_heap_fragment sg prepared installed
             (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
             selected.(armv7a_continuation_sp) /\
           selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
           selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
           task_invocation_active (os_int_exit_ready_checkpoint true returned).(TskState)
             original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
           (forall irq_return cursor written middle final_cursor after,
             armv7a_restore_transition abi handler selected installed irq_return ->
             cursor.(kernel_restore_r0) = saved ->
             cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
             armv7a_restore_prefix_transition restore cursor irq_return written middle ->
             armv7a_restore_suffix_transition restore written middle final_cursor after ->
             kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
             (os_sched_stack_return_post environment kernel_program_inv sg original
                (armv7a_irq_fiq_mask saved) call_before **
              (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                 handler.(os_int_exit_handler_fragments) ** frame)) after /\
             (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                original (armv7a_irq_fiq_mask saved) 0 **
              (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                 handler.(os_int_exit_handler_fragments) ** frame)) after))).
Proof.
  intros environment critical arch Extra restore initial extra_resources extra_step extra_effect
    sg checkpoint original_node original suspended incoming first_selected first_node child_args child_name
    handler foreign_saved publication saved acquired call_before region args task_return lower old_frame upper
    before saved_heap frame abi focus payload updated first_state foreign entry parked Horigin Horiginal_node
    Horiginal_gen Hbinding Hcall Hslice Hmask Hactive Hrunning Hnesting Hinitial Hinitial_call
    Hinitial_fragments Hname Hhandler_call Hhandler_mask Hforeign_slice Hregion Hgeometry Hpublication
    Hsp Haddress Hextension Hextra Henter Hexit Hpublish Hsource Hpre Hsave.
  assert (Horiginal_lease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  match type of Hpre with ?P before => assert (Hexpose : P |--
    coq_prop (first_selected.(armv7a_continuation_stack) = incoming /\
      (task_stack_key incoming = armv7a_call_focus_key focus ->
        armv7a_continuation_focus_binding focus first_selected) /\
      sched_current_ready_at first_state.(TskState) first_state.(SchedState)
        incoming.(stackLeaseSlot) first_node /\
      first_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
      UCOS2_state_inv sg first_state) && TT) end.
  { unfold os_sched_source_selected_post, UCOS2_inv; entailer!; try tauto; intros ? ?; exact I. }
  destruct (Hexpose before Hpre) as [[Hfirst_lease [Hfocused [Hready [Hfirst_gen Hvalid]]]] _].
  assert (Hdifferent : task_stack_key incoming <> armv7a_call_focus_key focus).
  { intros Heq; specialize (Hfocused Heq); destruct Hfocused as [Hfocused _]; congruence. }
  assert (Habsent : first_state.(TskState).(parkedTaskStacks) (task_stack_key incoming) = None).
  { unfold first_state, os_sched_install_context; cbn [replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks parkedTaskStacks]; apply task_stack_take_lookup. }
  assert (Hpending : entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { change (first_state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
    unfold first_state, os_sched_install_context; cbn [replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks parkedTaskStacks].
    rewrite task_stack_take_lookup_other by congruence.
    unfold focus, armv7a_call_focus_key, armv7a_call_focus; cbn [armv7a_focus_call].
    rewrite task_stack_park_fragments_lookup; unfold payload; rewrite Horiginal_lease; reflexivity. }
  assert (Hpointer : task_saved_pointer_at entry suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { exists (task_set_saved_sp original_node suspended.(armv7a_continuation_sp)).
    rewrite Horiginal_lease; split; [|split; [exact Horiginal_gen|reflexivity]].
    change (updated.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) =
      Some (task_set_saved_sp original_node suspended.(armv7a_continuation_sp))).
    unfold updated, os_sched_save_current_sp; rewrite Horiginal_node.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hregistered_active : task_invocation_active entry.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { apply task_begin_invocation_preserves_invocation_active; [|exact Hactive].
    pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hfirst_id : first_node.(taskID) = incoming.(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hactive_nodes.
    destruct Hactive_nodes as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact (proj1 Hready)].
    apply Hdomain; eauto using (proj1 Hready). }
  pose proof (task_create_selected_initial_entry_focused_world environment initial sg child_args child_name
    focus incoming first_selected first_node first_state Hrunning Hinitial Hinitial_call
    Hinitial_fragments Habsent Hname) as Hregister.
  cbv zeta in Hregister; fold abi foreign entry in Hregister.
  match type of Hpre with ?P before => assert (Hregistered : P |--
    coq_prop (task_create_source_entry sg child_args child_name foreign entry /\
      task_stack_live_coverage entry.(TskState) (task_stack_call_active_key foreign)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) foreign
       (armv7a_irq_fiq_mask first_selected.(armv7a_continuation_cpsr)) **
     kernel_program_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
       entry.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
      frame))) end.
  { sepcon_assoc_change; sep_apply_l_atomic Hregister; entailer!. }
  destruct (Hregistered before Hpre) as [[Hentry Hcoverage] Howned].
  match type of Howned with ?P before => assert (Hirq : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) handler **
    (kernel_program_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame))) end.
  { unfold os_int_exit_frame_save_pre; rewrite Hhandler_call, Hhandler_mask; entailer!. }
  assert (Hforeign_lease : foreign.(os_sched_call_stack) = incoming)
    by (unfold foreign, armv7a_initial_call; cbn; exact Hfirst_lease).
  assert (Hforeign_current : entry.(SchedState).(curTaskID) = Some foreign.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite Hforeign_lease; exact (proj1 (proj2 Hready))).
  assert (Hforeign_node : entry.(TskState).(inUsedTaskStates) foreign.(os_sched_call_stack).(stackLeaseSlot) =
    Some first_node) by (rewrite Hforeign_lease; exact (proj1 Hready)).
  assert (Hforeign_absent : entry.(TskState).(parkedTaskStacks) (task_stack_key foreign.(os_sched_call_stack)) = None)
    by (rewrite Hforeign_lease; exact Habsent).
  assert (Hforeign_id : first_node.(taskID) = foreign.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite Hforeign_lease; exact Hfirst_id).
  assert (Hforeign_gen : first_node.(taskGeneration) = foreign.(os_sched_call_stack).(stackLeaseGeneration))
    by (rewrite Hforeign_lease; exact Hfirst_gen).
  assert (Hcovered : task_stack_live_coverage entry.(TskState) (Some (task_stack_key foreign.(os_sched_call_stack))))
    by exact Hcoverage.
  pose proof (task_create_foreign_irq_registry_source environment critical Extra extra_resources extra_step
    extra_effect sg entry first_node handler foreign_saved publication original suspended
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame)
    before saved_heap) as Hregistry_source.
  cbv zeta in Hregistry_source; fold abi focus payload in Hregistry_source.
  rewrite Hhandler_call in Hregistry_source.
  specialize (Hregistry_source Hbinding Hcall Hregistered_active Hpointer Hforeign_slice
    Hrunning Hnesting Hforeign_current Hforeign_node Hforeign_id Hforeign_gen Hforeign_absent Hpending
    (Haddress _) Hregion Hgeometry Hpublication Hsp Hcovered Hextension Hextra Henter Hexit Hpublish Hsource
    (Hirq before Howned) Hsave).
  destruct Hregistry_source as [registry_heap [Hwrites [Hstores Htrace_return]]].
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (Htrace_return closed_heap Htrace)
    as [returned [stopped [returned_origin [Hstates [Hsources [Hreturned_pointer [Hlive Hworld]]]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_running Hswitch Hnonempty Hhigh Hhook.
  destruct (task_create_sched_selected_irq_return_post environment critical arch restore sg returned
    handler original suspended saved acquired call_before region args task_return lower old_frame upper
    closed_heap frame Horigin Hbinding Hcall Hslice Hmask (Hlive Hnormal) Hreturned_pointer
    Hreturned_running Hswitch Hnonempty Hhigh Hhook (Haddress _) Hworld)
    as [prepared [installed [selected [Hprefix [Hempty [Hhook_source [Hinstall [Hcpsr
      [Hregisters [Hhooked_live Hfinal]]]]]]]]]].
  exists prepared, installed, selected; split; [exact Hprefix|]. split; [exact Hempty|].
  split; [exact Hinstall|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  split; [exact Hhooked_live|].
  intros irq_return cursor written middle final_cursor after Hirq_return Hr0 Hcursor Hprefix_return Hsuffix.
  destruct (Hfinal irq_return cursor written middle final_cursor after Hirq_return Hr0 Hcursor
    Hprefix_return Hsuffix) as [Hexecution [Hordinary [Hpost Hpublic]]].
  exact (conj Hexecution (conj Hpost Hpublic)).
Qed.

(** A saved foreign destination resumes its OLD invocation. Unlike the
    initial-entry branch above, it neither allocates a fresh registration
    nor interprets the dormant owner as an initial-entry owner. The old
    Save's token and inside handle are explicit retained resources (the
    retained frame of [task_create_pending_sched_switch_source] has exactly
    this shape). They are not consequences of selected execution authority.

    Consume that old call's actual local MSR/BX, then an IRQ at its return
    PC on the SAME returned heap. This is an uninterrupted local Restore
    followed by one IRQ, not an IRQ while the selected CPSR is still 192.
    The rest is the same verified registry and original-frame consumer as
    the first-entry branch. No sequential-call ABI or application action
    is postulated, and no claim is made that every registry trace returns. *)
Lemma task_create_selected_saved_call_irq_return_post : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg checkpoint original_node original suspended incoming
  first_selected first_node previous previous_saved previous_acquired
  handler foreign_saved publication saved acquired call_before region args task_return lower old_frame upper
  cursor written middle final_cursor released before saved_heap (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let updated := os_sched_save_current_sp checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let state := os_sched_install_context original suspended.(armv7a_continuation_fragments)
    incoming updated in
  let foreign := armv7a_continuation_resumed_call first_selected previous in
  let parked := armv7a_irq_live_parked_state state foreign foreign_saved.(armv7a_continuation_sp)
    foreign_saved.(armv7a_continuation_fragments) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  checkpoint.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some original_node ->
  original_node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  state.(SchedState).(isRunning) = true -> state.(IntrState).(intNesting) = 0 ->
  first_selected.(armv7a_continuation_call) = Some previous -> previous <> original ->
  armv7a_irq_fiq_mask first_selected.(armv7a_continuation_cpsr) = 192 ->
  cursor.(kernel_restore_r0) = previous_saved ->
  cursor.(kernel_restore_current_cpsr) = first_selected.(armv7a_continuation_cpsr) ->
  handler.(os_int_exit_interrupted_call) = foreign ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask previous_saved ->
  handler.(os_int_exit_interrupted_pc) = cursor.(kernel_restore_lr) ->
  armv7a_task_frame_slice foreign_saved ->
  valid_task_stack_region foreign.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range foreign.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    foreign_saved.(armv7a_continuation_fragments) ->
  task_publication_happened state.(TskState) publication
    foreign.(os_sched_call_stack).(stackLeaseSlot) foreign.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range foreign.(os_sched_call_stack).(stackLeaseRegion)
    foreign_saved.(armv7a_continuation_sp) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut initial next returned, extra_effect sg cut initial next returned ->
    UCOS2_state_inv sg initial ->
    task_saved_pointer_at initial suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None extra_effect ->
  (os_sched_source_selected_post environment.(task_stack_call_external)
     environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
     sg focus incoming first_selected first_node state ** unmap_table_rep sg **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token previous_saved previous.(os_sched_call_invocation) previous.(os_sched_call_origin)) **
    critical_region_inside critical sg previous.(os_sched_call_invocation) previous_acquired **
    interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  armv7a_save_transition abi handler foreign_saved released saved_heap ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  final_cursor.(kernel_restore_return_word) = Some handler.(os_int_exit_interrupted_pc) /\
  released.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes foreign_saved)
      released.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg state
      foreign.(os_sched_call_stack).(stackLeaseSlot) foreign_saved.(armv7a_continuation_sp))
      saved_heap registry_heap /\
    (forall closed_heap,
      kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
        KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
          KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          original.(os_sched_call_invocation) None original.(os_sched_call_origin)
          parked stopped returned_origin returned /\
        (stopped = false ->
         returned.(SchedState).(isRunning) = true ->
         os_int_exit_requests_switch true returned = true ->
         returned.(SchedState).(readyList) <> [] ->
         (os_int_exit_ready_checkpoint true returned).(SchedState).(highRdyTid) =
           Some original.(os_sched_call_stack).(stackLeaseSlot) ->
         kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg
           (os_int_exit_ready_checkpoint true returned) (os_int_exit_ready_checkpoint true returned) ->
         exists prepared installed selected,
           os_int_exit_source_switch_prefix_execution sg closed_heap prepared /\
           kernel_heap_execution [] prepared prepared /\
           sched_install_heap_fragment sg prepared installed
             (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
             selected.(armv7a_continuation_sp) /\
           selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
           selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
           task_invocation_active (os_int_exit_ready_checkpoint true returned).(TskState)
             original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
           (forall irq_return return_cursor return_written return_middle return_final after,
             armv7a_restore_transition abi handler selected installed irq_return ->
             return_cursor.(kernel_restore_r0) = saved ->
             return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
             armv7a_restore_prefix_transition restore return_cursor irq_return return_written return_middle ->
             armv7a_restore_suffix_transition restore return_written return_middle return_final after ->
             kernel_call_restore_uninterrupted_execution arch return_cursor irq_return return_final after /\
             (os_sched_stack_return_post environment kernel_program_inv sg original
                (armv7a_irq_fiq_mask saved) call_before **
              (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                 handler.(os_int_exit_handler_fragments) ** frame)) after /\
             (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                original (armv7a_irq_fiq_mask saved) 0 **
              (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                 handler.(os_int_exit_handler_fragments) ** frame)) after))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg checkpoint
    original_node original suspended incoming first_selected first_node previous previous_saved previous_acquired
    handler foreign_saved publication saved acquired call_before region args task_return lower old_frame upper
    cursor written middle final_cursor released before saved_heap frame abi focus payload updated state foreign parked
    Horigin Horiginal_node Horiginal_gen Hbinding Hcall Hslice Hmask Hactive Hrunning Hnesting
    Hprevious_call Hprevious_different Hprevious_mask Hr0 Hcursor Hhandler_call Hhandler_mask Hhandler_pc
    Hforeign_slice Hregion Hgeometry Hpublication Hsp Haddress Hextension Hextra Henter Hexit Hpublish Hsource
    Hpre Hprefix_return Hsuffix_return Hsave.
  assert (Horiginal_lease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  match type of Hpre with ?P before => assert (Hexpose : P |--
    coq_prop (first_selected.(armv7a_continuation_stack) = incoming /\
      (task_stack_key incoming = armv7a_call_focus_key focus ->
        armv7a_continuation_focus_binding focus first_selected) /\
      sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) first_node /\
      first_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
      task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming)) /\
      UCOS2_state_inv sg state) && TT) end.
  { unfold os_sched_source_selected_post, UCOS2_inv; entailer!; try tauto; intros ? ?; exact I. }
  destruct (Hexpose before Hpre) as [[Hfirst_lease [Hfocused [Hready [Hfirst_gen [Hcoverage Hvalid]]]]] _].
  assert (Hdifferent : task_stack_key incoming <> armv7a_call_focus_key focus).
  { intros Heq; specialize (Hfocused Heq); destruct Hfocused as [Hfocused _].
    change (first_selected.(armv7a_continuation_call) = Some original) in Hfocused; congruence. }
  assert (Habsent : state.(TskState).(parkedTaskStacks) (task_stack_key incoming) = None).
  { unfold state, os_sched_install_context; cbn [replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks parkedTaskStacks]; apply task_stack_take_lookup. }
  assert (Hpending : state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { unfold state, os_sched_install_context; cbn [replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks parkedTaskStacks].
    rewrite task_stack_take_lookup_other by congruence.
    unfold focus, armv7a_call_focus_key, armv7a_call_focus; cbn [armv7a_focus_call].
    rewrite task_stack_park_fragments_lookup; unfold payload; rewrite Horiginal_lease; reflexivity. }
  assert (Hpointer : task_saved_pointer_at state suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { exists (task_set_saved_sp original_node suspended.(armv7a_continuation_sp)).
    rewrite Horiginal_lease; split; [|split; [exact Horiginal_gen|reflexivity]].
    change (updated.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) =
      Some (task_set_saved_sp original_node suspended.(armv7a_continuation_sp))).
    unfold updated, os_sched_save_current_sp; rewrite Horiginal_node.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hfirst_id : first_node.(taskID) = incoming.(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hactive_nodes.
    destruct Hactive_nodes as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact (proj1 Hready)].
    apply Hdomain; eauto using (proj1 Hready). }
  match type of Hpre with ?P before => assert (Hrestore_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      foreign.(os_sched_call_invocation) foreign.(os_sched_call_origin) previous_saved previous_acquired **
    os_sched_context_resources environment.(task_stack_call_external) foreign **
    (kernel_program_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
      frame))) end.
  { unfold os_sched_source_selected_post; Intros.
    unfold armv7a_task_restored_execution; rewrite Hprevious_call, Hprevious_mask; fold foreign.
    unfold critical_region_masked, kernel_call_execution_owned.
    rewrite kernel_program_inv_split_unmap.
    unfold foreign, armv7a_continuation_resumed_call; cbn [os_sched_call_invocation os_sched_call_origin].
    entailer!. }
  assert (Hcursor_mask : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    by (rewrite Hcursor; exact Hprevious_mask).
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg foreign
    previous_saved previous_acquired cursor before written middle final_cursor released _ Hr0 Hcursor_mask
    (Hrestore_input before Hpre) Hprefix_return Hsuffix_return)
    as [Hreturn_execution [Hreturn_pc [Hmemory Howned]]].
  split; [exact Hreturn_execution|]. split; [rewrite Hhandler_pc; exact Hreturn_pc|].
  split; [exact Hmemory|].
  match type of Howned with ?P released => assert (Hirq : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) handler **
    (kernel_program_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame))) end.
  { unfold os_int_exit_frame_save_pre; rewrite Hhandler_call, Hhandler_mask; entailer!. }
  assert (Hforeign_lease : foreign.(os_sched_call_stack) = incoming)
    by (unfold foreign, armv7a_continuation_resumed_call; cbn; exact Hfirst_lease).
  assert (Hforeign_current : state.(SchedState).(curTaskID) = Some foreign.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite Hforeign_lease; exact (proj1 (proj2 Hready))).
  assert (Hforeign_node : state.(TskState).(inUsedTaskStates) foreign.(os_sched_call_stack).(stackLeaseSlot) =
    Some first_node) by (rewrite Hforeign_lease; exact (proj1 Hready)).
  assert (Hforeign_absent : state.(TskState).(parkedTaskStacks) (task_stack_key foreign.(os_sched_call_stack)) = None)
    by (rewrite Hforeign_lease; exact Habsent).
  assert (Hforeign_id : first_node.(taskID) = foreign.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite Hforeign_lease; exact Hfirst_id).
  assert (Hforeign_gen : first_node.(taskGeneration) = foreign.(os_sched_call_stack).(stackLeaseGeneration))
    by (rewrite Hforeign_lease; exact Hfirst_gen).
  assert (Hcovered : task_stack_live_coverage state.(TskState) (Some (task_stack_key foreign.(os_sched_call_stack))))
    by (rewrite Hforeign_lease; exact Hcoverage).
  pose proof (task_create_foreign_irq_registry_source environment critical Extra extra_resources extra_step
    extra_effect sg state first_node handler foreign_saved publication original suspended
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame)
    released saved_heap) as Hregistry_source.
  cbv zeta in Hregistry_source; fold abi focus payload in Hregistry_source.
  rewrite Hhandler_call in Hregistry_source.
  specialize (Hregistry_source Hbinding Hcall Hactive Hpointer Hforeign_slice
    Hrunning Hnesting Hforeign_current Hforeign_node Hforeign_id Hforeign_gen Hforeign_absent Hpending
    (Haddress _) Hregion Hgeometry Hpublication Hsp Hcovered Hextension Hextra Henter Hexit Hpublish Hsource
    (Hirq released Howned) Hsave).
  destruct Hregistry_source as [registry_heap [Hwrites [Hstores Htrace_return]]].
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (Htrace_return closed_heap Htrace)
    as [returned [stopped [returned_origin [Hstates [Hsources [Hreturned_pointer [Hlive Hworld]]]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_running Hswitch Hnonempty Hhigh Hhook.
  destruct (task_create_sched_selected_irq_return_post environment critical arch restore sg returned
    handler original suspended saved acquired call_before region args task_return lower old_frame upper
    closed_heap frame Horigin Hbinding Hcall Hslice Hmask (Hlive Hnormal) Hreturned_pointer
    Hreturned_running Hswitch Hnonempty Hhigh Hhook (Haddress _) Hworld)
    as [prepared [installed [selected [Hprefix [Hempty [Hhook_source [Hinstall [Hcpsr
      [Hregisters [Hhooked_live Hfinal]]]]]]]]]].
  exists prepared, installed, selected; split; [exact Hprefix|]. split; [exact Hempty|].
  split; [exact Hinstall|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  split; [exact Hhooked_live|].
  intros irq_return return_cursor return_written return_middle return_final after Hirq_return
    Hreturn_r0 Hreturn_cursor Hfinal_prefix Hfinal_suffix.
  destruct (Hfinal irq_return return_cursor return_written return_middle return_final after Hirq_return
    Hreturn_r0 Hreturn_cursor Hfinal_prefix Hfinal_suffix) as [Hexecution [Hordinary [Hpost Hpublic]]].
  exact (conj Hexecution (conj Hpost Hpublic)).
Qed.

(** Consume the actual pending-call install/read/restore producer at its
    returning destination, then the original call's final MSR/BX. The
    original saved mask and inside handle are retained resources, not a
    duplicate running token. The current world comes from the actual
    destination producer, not a frame of the world before switching.

    The public TaskCreate success contract needs that same-call world,
    not an invented flat client trace from the first foreign installation
    to the last take. This theorem intentionally starts at the final
    destination cut; the earlier switch/client source must produce that
    cut, including the original invocation's still-active registration.
    Installing the context changes the parked map/current cache, not that
    registration. It neither asserts termination nor classifies all scheduler/IRQ
    executions as this returning branch. No callee Ensure is assumed. *)
Lemma task_create_sched_pending_return_resources :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg context outgoing hooked original suspended saved acquired heap
    (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
     unmap_table_rep sg ** frame))) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      armv7a_restore_prefix_transition restore cursor restored written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
      kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original /\
      kernel_call_task_source (armv7a_continuation_resumed_call selected original)
        (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked) /\
      (exists node,
        (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked).(TskState).(inUsedTaskStates)
          original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
        is_effectively_ready node.(stat) node.(dly) = true) /\
      (kernel_stack_call_closed abi kernel_program_inv sg
         (task_stack_call_active_key (armv7a_continuation_resumed_call selected original))
         (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask saved)
         (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked) ** frame) after).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked original suspended saved acquired heap
    frame abi focus Horigin Hbinding Hcall Hslice Hmask Hsaved
    Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hlive Hpre.
  destruct (task_create_sched_pending_return_source environment critical arch task_abi restore sg context
    outgoing hooked original suspended saved acquired heap frame Horigin Hbinding Hcall Hslice Hmask
    Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre)
    as [installed [selected [node [Hinstall [Hreads [Hsp [Hcpsr [Hregisters Hrestore]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hsp|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros restored Hrun cursor written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix.
  destruct (Hrestore restored Hrun) as [Hsame [Hsource [Hselected [Hmasked Hreturn]]]].
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  set (current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked) in *.
  assert (Hordinary : kernel_call_task_source returned current).
  { pose proof Hsame as [Hinvocation [Hsameorigin Hstack]].
    unfold kernel_call_task_source; split.
    - rewrite Hsameorigin, Hstack; exact Horigin.
    - split.
      + rewrite Hinvocation, Hsameorigin.
        change (task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
          original.(os_sched_call_origin)); exact Hlive.
      + unfold task_execution_current; rewrite Hsameorigin, Horigin.
        change (hooked.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
        exact (proj1 Hdestination). }
  assert (Hcursor_mask : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    by (rewrite Hcursor, Hcpsr; exact Hmask).
  match type of Hmasked with ?P restored => assert (Hopen : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) returned **
    (kernel_stack_inv abi kernel_program_inv sg (task_stack_call_active_key returned) current ** frame))
    by (unfold kernel_stack_call_masked; entailer!) end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg returned saved
    acquired cursor restored written middle final_cursor after _ Hr0 Hcursor_mask
    (Hopen restored Hmasked) Hprefix Hsuffix) as [Hexecution [Hlr [Hmemory Howned]]].
  assert (Hready : exists selected_node,
    current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some selected_node /\
    is_effectively_ready selected_node.(stat) selected_node.(dly) = true).
  { match type of Hselected with ?P restored => assert (Hobserve : P |--
      coq_prop (sched_current_ready_at current.(TskState) current.(SchedState)
        original.(os_sched_call_stack).(stackLeaseSlot) node) && TT) end.
    { unfold os_sched_source_selected_post; entailer!; intros ? ?; exact I. }
    pose proof (proj1 (Hobserve restored Hselected)) as Hready_node.
    exists node; exact (conj (proj1 Hready_node) (proj2 (proj2 (proj2 (proj2 Hready_node))))). }
  assert (Hexact : (kernel_stack_call_closed abi kernel_program_inv sg
    (task_stack_call_active_key returned) returned (armv7a_irq_fiq_mask saved) current ** frame) after).
  { match type of Howned with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) by (unfold kernel_stack_call_closed; entailer!) end end.
    exact (Hclose after Howned). }
  exact (conj Hexecution (conj Hsame (conj Hordinary (conj Hready Hexact)))).
Qed.

(** Compatibility projection; the source-produced exact owner is exposed above. *)
Lemma task_create_sched_pending_return_post :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg context outgoing hooked original suspended saved acquired heap
    call_before region args task_return lower old_frame upper (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
     unmap_table_rep sg ** frame))) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      armv7a_restore_prefix_transition restore cursor restored written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
      (os_sched_stack_return_post environment kernel_program_inv sg original
         (armv7a_irq_fiq_mask saved) call_before ** frame) after /\
      (task_create_stack_post environment critical sg region args task_return lower old_frame upper
         original (armv7a_irq_fiq_mask saved) 0 ** frame) after).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked original suspended saved acquired heap
    call_before region args task_return lower old_frame upper frame abi focus Horigin Hbinding Hcall Hslice Hmask Hsaved
    Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hlive Hpre.
  destruct (task_create_sched_pending_return_resources environment critical arch task_abi restore sg context
    outgoing hooked original suspended saved acquired heap frame Horigin Hbinding Hcall Hslice Hmask Hsaved
    Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hlive Hpre)
    as [installed [selected [Hinstall [Hreads [Hsp [Hcpsr [Hregisters Hreturn]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hsp|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros restored Hrun cursor written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix.
  destruct (Hreturn restored Hrun cursor written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix)
    as [Hexecution [Hsame [Hsource [Hready Howned]]]].
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  set (current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked) in *.
  assert (Hpost : (os_sched_stack_return_post environment kernel_program_inv sg original
    (armv7a_irq_fiq_mask saved) call_before ** frame) after).
  { match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { assert (Hactive : task_stack_call_active_key original = task_stack_call_active_key returned).
      { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
      unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post.
      Exists returned current; rewrite Hactive; entailer!. }
    exact (Hclose after Howned). }
  split; [exact Hexecution|]. split; [exact Hpost|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (os_sched_stack_return_post_returns_create environment critical sg original original
      (armv7a_irq_fiq_mask saved) call_before region args task_return lower old_frame upper
      ltac:(unfold task_tcb_init_stack_same_call; auto)); entailer!. }
  exact (Hclose after Hpost).
Qed.
