Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_irq_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual no-switch C prefix is followed by Restore's MSR, an IRQ
    save, kernel nesting/SP stores, ONE registered heap/state/source trace,
    the original-call wrapper restore, and Restore's BX.  The released
    [os_sched_prefix_state state] is deliberately not called the returned
    state: IRQ clients may have changed it.  Their CURRENT owned stack
    map, not a stale framed map, supplies the public Create success post.

    This is a normal-return source branch. The current-task test selects
    return to this invocation; it does not assert eventual return or forbid
    other selected destinations. Extra handler/client effects must supply
    their actual registered resource/source proofs. No contract for an
    arbitrary application/handler implementation is silently introduced. *)
Lemma task_create_sched_nonswitch_irq_return_history : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg state node handler suspended publication
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let released := os_sched_prefix_state state in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  armv7a_task_frame_slice suspended ->
  state.(SchedState).(isRunning) = true -> state.(IntrState).(intNesting) = 0 ->
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
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
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None extra_effect ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved state **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg state **
   task_tcb_init_stack_covered_capsules environment state ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg before prefix_heap /\
    (forall written irq_input saved_heap,
      armv7a_restore_prefix_transition restore cursor prefix_heap written irq_input ->
      armv7a_save_transition abi handler suspended irq_input saved_heap ->
      exists registry_heap,
        written = kernel_restore_write_cpsr cursor /\
        kernel_heap_writes (armv7a_continuation_save_writes suspended)
          irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
        kernel_heap_execution (armv7a_irq_live_entry_writes sg released
          call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
          saved_heap registry_heap /\
        (forall closed_heap,
          kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
            KernelClientHeapClosed closed_heap ->
          exists returned stopped returned_origin,
            kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
              KernelClientHeapClosed returned /\
            kernel_resumption_task_source_trace environment.(task_stack_call_external)
              environment.(task_stack_call_port) critical.(critical_region_clients) sg
              call.(os_sched_call_invocation) None call.(os_sched_call_origin)
              parked stopped returned_origin returned /\
            (returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
             exists selected,
               armv7a_irq_restore_pointer_reads sg closed_heap
                 (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
                 selected.(armv7a_continuation_sp) /\
               selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
               selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
               (forall irq_return resume_cursor final_cursor after,
                 armv7a_restore_transition abi handler selected closed_heap irq_return ->
                 resume_cursor.(kernel_restore_msr_word) = Some
                   (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
                     cursor.(kernel_restore_r0)) ->
                 resume_cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
                 armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
                 kernel_call_restore_history environment critical sg call released
                   (armv7a_continuation_resumed_call selected call)
                   (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) /\
                 final_cursor.(kernel_restore_return_word) = Some selected.(armv7a_continuation_lr) /\
                 task_stack_live_coverage
                   (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState)
                   (Some (task_stack_key call.(os_sched_call_stack))) /\
                 (kernel_call_execution_owned environment.(task_stack_call_external)
                    environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
                    (armv7a_irq_fiq_mask saved) **
                  (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
                   task_tcb_init_stack_covered_capsules environment
                     (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
                   unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                     handler.(os_int_exit_handler_fragments) ** frame)) after /\
                 (os_sched_source_return_post environment critical sg call
                    (armv7a_irq_fiq_mask saved) released **
                  (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                     handler.(os_int_exit_handler_fragments) ** frame)) after /\
                 (task_create_stack_covered_success_post environment critical sg call
                    (armv7a_irq_fiq_mask saved) **
                  (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                     handler.(os_int_exit_handler_fragments) ** frame)) after /\
                 (stopped = false ->
                  (os_sched_stack_return_post environment kernel_program_inv sg call
                     (armv7a_irq_fiq_mask saved) state **
                   (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                      handler.(os_int_exit_handler_fragments) ** frame)) after))))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg state node
    handler suspended publication saved cursor before frame call abi released parked focus payload
    Horigin Hnoswitch Hnonempty Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Hextra
    Henter Hexit Hpublish Hsource Hpre.
  match type of Hpre with ?P before => assert (Hprefix_input : P |--
    UCOS2_inv sg state ** unmap_table_rep sg **
    (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved state ** task_tcb_init_stack_context environment call **
     task_tcb_init_stack_covered_capsules environment state **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) by entailer!
  end.
  destruct (os_sched_source_nonswitch_prefix_resources sg state _ before Hnoswitch Hnonempty
    (Hprefix_input before Hpre)) as [prefix_heap [Hprefix Hafter_prefix]].
  exists prefix_heap; split; [exact Hprefix|].
  intros written irq_input saved_heap Hrestore Hsave.
  assert (Htasks : released.(TskState) = state.(TskState)) by reflexivity.
  assert (Hsched : released.(SchedState).(isRunning) = state.(SchedState).(isRunning) /\
    released.(SchedState).(curTaskID) = state.(SchedState).(curTaskID)).
  { unfold released, os_sched_prefix_state, os_sched_ready_checkpoint.
    destruct (os_sched_selection_enabled state); destruct (os_sched_requests_switch state);
      split; reflexivity. }
  assert (Hreleased_running : released.(SchedState).(isRunning) = true)
    by (rewrite (proj1 Hsched); exact Hrunning).
  assert (Hreleased_current : released.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)) by (rewrite (proj2 Hsched); exact Hcurrent).
  match type of Hafter_prefix with ?P prefix_heap => assert (Hdeposit_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved state ** task_tcb_init_stack_context environment call **
    UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released **
    unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame) by
    (change (task_tcb_init_stack_covered_capsules environment released) with
      (task_tcb_init_stack_covered_capsules environment state); entailer!)
  end.
  assert (Hsource_eq : kernel_call_task_source call released = kernel_call_task_source call state).
  { unfold kernel_call_task_source, task_execution_current.
    rewrite Htasks; destruct call.(os_sched_call_origin); [reflexivity|].
    rewrite (proj2 Hsched); reflexivity. }
  assert (Hpost_eq : os_sched_stack_return_post environment kernel_program_inv sg call
      (armv7a_irq_fiq_mask saved) released =
    os_sched_stack_return_post environment kernel_program_inv sg call
      (armv7a_irq_fiq_mask saved) state).
  { unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post.
    rewrite Hsource_eq; reflexivity. }
  rewrite <- Hpost_eq.
  exact (task_create_stack_restore_irq_return_history environment critical arch Extra restore
    extra_resources extra_step extra_effect sg state released node handler suspended publication
    saved cursor prefix_heap frame Horigin Hslice Hreleased_running Hnesting Hreleased_current
    Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask
    Hhandler Hextension Hextra Henter Hexit Hpublish Hsource
    (Hdeposit_input prefix_heap Hafter_prefix) written irq_input saved_heap Hrestore Hsave).
Qed.

(** Historical restricted projection, preserving its exact old statement.
    It consumes the restricted local suffix theorem, not the computed-word
    source history. This is not a complete OS_Sched Ensure. *)
Lemma task_create_sched_nonswitch_irq_return : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg state node handler suspended publication
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let released := os_sched_prefix_state state in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  armv7a_task_frame_slice suspended ->
  state.(SchedState).(isRunning) = true -> state.(IntrState).(intNesting) = 0 ->
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
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
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None extra_effect ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved state **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg state **
   task_tcb_init_stack_covered_capsules environment state ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg before prefix_heap /\
    (forall written irq_input saved_heap,
      armv7a_restore_prefix_transition restore cursor prefix_heap written irq_input ->
      armv7a_save_transition abi handler suspended irq_input saved_heap ->
      exists registry_heap,
        written = kernel_restore_write_cpsr cursor /\
        kernel_heap_writes (armv7a_continuation_save_writes suspended)
          irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
        kernel_heap_execution (armv7a_irq_live_entry_writes sg released
          call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
          saved_heap registry_heap /\
        (forall closed_heap,
          kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
            KernelClientHeapClosed closed_heap ->
          exists returned stopped returned_origin,
            kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
              KernelClientHeapClosed returned /\
            kernel_resumption_task_source_trace environment.(task_stack_call_external)
              environment.(task_stack_call_port) critical.(critical_region_clients) sg
              call.(os_sched_call_invocation) None call.(os_sched_call_origin)
              parked stopped returned_origin returned /\
            (returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
             exists selected,
               armv7a_irq_restore_pointer_reads sg closed_heap
                 (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
                 selected.(armv7a_continuation_sp) /\
               selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
               selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
               (forall irq_return resume_cursor final_cursor after,
                 armv7a_restore_transition abi handler selected closed_heap irq_return ->
                 resume_cursor.(kernel_restore_msr_word) = Some saved ->
                 resume_cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
                 armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
                 final_cursor.(kernel_restore_return_word) = Some selected.(armv7a_continuation_lr) /\
                 task_stack_live_coverage
                   (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState)
                   (Some (task_stack_key call.(os_sched_call_stack))) /\
                 (kernel_call_execution_owned environment.(task_stack_call_external)
                    environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
                    (armv7a_irq_fiq_mask saved) **
                  (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
                   task_tcb_init_stack_covered_capsules environment
                     (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
                   unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                     handler.(os_int_exit_handler_fragments) ** frame)) after /\
                 (task_create_stack_covered_success_post environment critical sg call
                    (armv7a_irq_fiq_mask saved) **
                  (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                     handler.(os_int_exit_handler_fragments) ** frame)) after)))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg state node
    handler suspended publication saved cursor before frame call abi released parked focus payload
    Horigin Hnoswitch Hnonempty Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Hextra
    Henter Hexit Hpublish Hsource Hpre.
  match type of Hpre with ?P before => assert (Hprefix_input : P |--
    UCOS2_inv sg state ** unmap_table_rep sg **
    (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved state ** task_tcb_init_stack_context environment call **
     task_tcb_init_stack_covered_capsules environment state **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) by entailer!
  end.
  destruct (os_sched_source_nonswitch_prefix_resources sg state _ before Hnoswitch Hnonempty
    (Hprefix_input before Hpre)) as [prefix_heap [Hprefix Hafter_prefix]].
  exists prefix_heap; split; [exact Hprefix|].
  intros written irq_input saved_heap Hrestore Hsave.
  assert (Htasks : released.(TskState) = state.(TskState)) by reflexivity.
  assert (Hsched : released.(SchedState).(isRunning) = state.(SchedState).(isRunning) /\
    released.(SchedState).(curTaskID) = state.(SchedState).(curTaskID)).
  { unfold released, os_sched_prefix_state, os_sched_ready_checkpoint.
    destruct (os_sched_selection_enabled state); destruct (os_sched_requests_switch state);
      split; reflexivity. }
  assert (Hreleased_running : released.(SchedState).(isRunning) = true)
    by (rewrite (proj1 Hsched); exact Hrunning).
  assert (Hreleased_current : released.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)) by (rewrite (proj2 Hsched); exact Hcurrent).
  match type of Hafter_prefix with ?P prefix_heap => assert (Hdeposit_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved state ** task_tcb_init_stack_context environment call **
    UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released **
    unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame) by
    (change (task_tcb_init_stack_covered_capsules environment released) with
      (task_tcb_init_stack_covered_capsules environment state); entailer!)
  end.
  exact (task_create_stack_restore_irq_return environment critical arch Extra restore
    extra_resources extra_step extra_effect sg state released node handler suspended publication
    saved cursor prefix_heap frame Horigin Hslice Hreleased_running Hnesting Hreleased_current
    Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask
    Hhandler Hextension Hextra Henter Hexit Hpublish Hsource
    (Hdeposit_input prefix_heap Hafter_prefix) written irq_input saved_heap Hrestore Hsave).
Qed.
