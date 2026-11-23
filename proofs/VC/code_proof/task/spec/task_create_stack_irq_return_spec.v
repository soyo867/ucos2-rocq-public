Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
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

(** Reusable actual Restore/IRQ return source cut. The caller supplies
    the saved/inside handles and the CURRENT released heap/map. MSR, IRQ
    save, nesting/SP stores, the one registered heap/state/source trace,
    selected original-call restore and BX are connected on their actual
    heaps. No scheduler C prefix is assumed or fabricated here.

    This live running-call branch retains Extra's actual resource/source
    contract and exposes current state, coverage and strong map before any
    TaskCreate projection. In the false-stop branch of this SAME registry
    trace it also preserves ordinary-call source into the current Scheduler
    post. It does not infer readiness or assert that every trace has stopped=false.
    Thus Sem/TCBInit may consume this segment without importing a fictional
    OS_Sched execution; their own source stages still supply those facts. *)
Lemma task_create_stack_restore_irq_return_history : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg entry released node handler suspended publication
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  released.(SchedState).(isRunning) = true -> released.(IntrState).(intNesting) = 0 ->
  released.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened released.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  task_stack_live_coverage released.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
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
     call.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg released **
   task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
    (forall written irq_input saved_heap,
      armv7a_restore_prefix_transition restore cursor before written irq_input ->
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
                     (armv7a_irq_fiq_mask saved) released **
                   (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                      handler.(os_int_exit_handler_fragments) ** frame)) after))))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg entry released
    node handler suspended publication saved cursor before frame call abi parked focus payload
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Hextra Henter Hexit Hpublish Hsource Hpre
    written irq_input saved_heap Hrestore Hsave.
  destruct (task_create_restore_irq_deposit environment critical arch restore sg entry released node
    handler suspended publication saved cursor before written irq_input saved_heap frame
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hpre
    Hrestore Hsave) as [registry_heap [Hwritten [Hwrites [Hstores [Hbinding [Hcall [Hsaved_mask
      [Hvalid [Hpointer Hregistry]]]]]]]]].
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  assert (Hcut : @kernel_client_heap_observer_cut Extra call.(os_sched_call_invocation) KernelClientHeapClosed)
    by exact I.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources extra_step extra_effect
    critical.(critical_region_clients) sg call suspended Hbinding Hcall Hslice Hextension Hextra
    Henter Hexit Hpublish Hsource KernelClientHeapClosed registry_heap closed_heap parked handler frame
    Hvalid Hpointer Htrace Hcut Hregistry)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hreturned_current.
  destruct (Hreturn Hreturned_current Haddress)
    as [selected [Hpointers [Hfocus [Hlease [Hselected_sp [Hcpsr [Hregisters [Hcovered Hresume]]]]]]]].
  exists selected; split; [exact Hpointers|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros irq_return resume_cursor final_cursor after Hirq_restore Hword Hlr Hsuffix.
  destruct (Hresume irq_return Hirq_restore) as [Hmemory Howned].
  rewrite Hsaved_mask in Howned.
  match type of Howned with ?P irq_return => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
      (armv7a_irq_fiq_mask saved) **
    (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     task_tcb_init_stack_covered_capsules environment
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame))
    by (unfold task_tcb_init_stack_covered_capsules; entailer!)
  end.
  assert (Hcomputed : (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
      (armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
        cursor.(kernel_restore_r0))) **
    (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     task_tcb_init_stack_covered_capsules environment
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) irq_return).
  { rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact (Hsuffix_input irq_return Howned). }
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call selected call) _ resume_cursor irq_return final_cursor after
    _ Hword Hcomputed Hsuffix) as [Hcursor [Hmemory_after Hafter]].
  rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hafter.
  assert (Hhistory : kernel_call_restore_history environment critical sg call released
    (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { eapply KernelCallRestoreIRQ with (restore := restore)
      (extra_step := extra_step) (extra_effect := extra_effect)
      (handler := handler) (suspended := suspended) (cursor := cursor)
      (before := before) (written := written) (irq_input := irq_input) (saved_heap := saved_heap)
      (registry_heap := registry_heap) (closed_heap := closed_heap) (returned := returned)
      (stopped := stopped) (returned_origin := returned_origin) (irq_return := irq_return)
      (resume_cursor := resume_cursor) (final_cursor := final_cursor) (after := after);
      try eassumption; try reflexivity. }
  split; [exact Hhistory|].
  split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - split; [exact Hcovered|]. split; [exact Hafter|]. split.
    + match type of Hafter with ?P after => assert (Hsource_post : P |--
        os_sched_source_return_post environment critical sg call (armv7a_irq_fiq_mask saved) released **
        (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) end.
      { unfold os_sched_source_return_post.
        Exists (armv7a_continuation_resumed_call selected call)
          (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
        unfold kernel_stack_inv, task_tcb_init_stack_covered_capsules, task_stack_call_active_key,
          armv7a_continuation_resumed_call.
        cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
        rewrite Horigin; entailer!.
        rewrite <- Horigin; exact Hhistory. }
      exact (Hsource_post after Hafter).
    + split.
      * match type of Hafter with ?P after => assert (Hpost : P |--
      task_create_stack_covered_success_post environment critical sg call (armv7a_irq_fiq_mask saved) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame)) end.
    { unfold task_create_stack_covered_success_post.
      Exists (armv7a_continuation_resumed_call selected call)
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
      unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_same_call,
        task_stack_call_active_key, armv7a_continuation_resumed_call, critical_region_outside.
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
      rewrite Horigin, critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
      unfold UCOS2_inv; entailer!. }
        exact (Hpost after Hafter).
      * intro Hnormal.
        assert (Hordinary : kernel_call_task_source call released ->
          kernel_call_task_source (armv7a_continuation_resumed_call selected call)
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
        { intros [_ [Hactive _]].
          assert (Hparked_active : task_invocation_active parked.(TskState)
            call.(os_sched_call_invocation) call.(os_sched_call_origin)).
          { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
              armv7a_irq_entry_counter_state, os_sched_save_current_sp.
            rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode.
            change (task_invocation_active
              (glob_task_set_usedtask released.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
                (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
              call.(os_sched_call_invocation) call.(os_sched_call_origin)).
            eapply task_set_saved_sp_preserves_invocation_active; eassumption. }
          pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _
            critical.(critical_region_clients) sg call.(os_sched_call_invocation) None
            call.(os_sched_call_origin) parked stopped returned_origin returned Hsources)) as Hinterval.
          rewrite Hnormal in Hinterval.
          destruct (critical_region_interval_transports_resources critical sg
            call.(os_sched_call_invocation) parked returned Hinterval Hvalid) as [_ [_ Hlive]].
          unfold kernel_call_task_source, armv7a_continuation_resumed_call.
          cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
          split; [rewrite Hlease; exact Horigin|]. split.
          - change (task_invocation_active returned.(TskState)
              call.(os_sched_call_invocation) call.(os_sched_call_origin)).
            apply Hlive; exact Hparked_active.
          - unfold task_execution_current; rewrite Horigin; exact Hreturned_current. }
        match type of Hafter with ?P after => assert (Hpost : P |--
          os_sched_stack_return_post environment kernel_program_inv sg call
            (armv7a_irq_fiq_mask saved) released **
          (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
             handler.(os_int_exit_handler_fragments) ** frame)) end.
        { unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post.
          Exists (armv7a_continuation_resumed_call selected call)
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
          unfold kernel_stack_call_closed, kernel_stack_inv, task_tcb_init_stack_covered_capsules.
          rewrite kernel_program_inv_split_unmap.
          unfold task_stack_call_active_key; rewrite Horigin.
          assert (Hsame : kernel_stack_call_same_call (armv7a_continuation_resumed_call selected call) call).
          { unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto. }
          entailer!. }
        exact (Hpost after Hafter).
Qed.

(** Historical restricted resource projection. Its old local BX premise
    identifies the cursor word with saved R0. This theorem does NOT produce
    a source history or claim that the actual earlier MSR wrote that value.
    Full source consumers use the computed-word history theorem above. *)
Lemma task_create_stack_restore_irq_return : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg entry released node handler suspended publication
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  released.(SchedState).(isRunning) = true -> released.(IntrState).(intNesting) = 0 ->
  released.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened released.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  task_stack_live_coverage released.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
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
     call.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg released **
   task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
    (forall written irq_input saved_heap,
      armv7a_restore_prefix_transition restore cursor before written irq_input ->
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
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg entry released
    node handler suspended publication saved cursor before frame call abi parked focus payload
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Hextra Henter Hexit Hpublish Hsource Hpre
    written irq_input saved_heap Hrestore Hsave.
  destruct (task_create_restore_irq_deposit environment critical arch restore sg entry released node
    handler suspended publication saved cursor before written irq_input saved_heap frame
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hpre
    Hrestore Hsave) as [registry_heap [Hwritten [Hwrites [Hstores [Hbinding [Hcall [Hsaved_mask
      [Hvalid [Hpointer Hregistry]]]]]]]]].
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  assert (Hcut : @kernel_client_heap_observer_cut Extra call.(os_sched_call_invocation) KernelClientHeapClosed)
    by exact I.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources extra_step extra_effect
    critical.(critical_region_clients) sg call suspended Hbinding Hcall Hslice Hextension Hextra
    Henter Hexit Hpublish Hsource KernelClientHeapClosed registry_heap closed_heap parked handler frame
    Hvalid Hpointer Htrace Hcut Hregistry)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hreturned_current.
  destruct (Hreturn Hreturned_current Haddress)
    as [selected [Hpointers [Hfocus [Hlease [Hselected_sp [Hcpsr [Hregisters [Hcovered Hresume]]]]]]]].
  exists selected; split; [exact Hpointers|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros irq_return resume_cursor final_cursor after Hirq_restore Hword Hlr Hsuffix.
  destruct (Hresume irq_return Hirq_restore) as [Hmemory Howned].
  rewrite Hsaved_mask in Howned.
  match type of Howned with ?P irq_return => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
      (armv7a_irq_fiq_mask saved) **
    (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     task_tcb_init_stack_covered_capsules environment
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame))
    by (unfold task_tcb_init_stack_covered_capsules; entailer!)
  end.
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call selected call) saved resume_cursor irq_return final_cursor after
    _ Hword (Hsuffix_input irq_return Howned) Hsuffix) as [Hcursor [Hmemory_after Hafter]].
  split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - split; [exact Hcovered|]. split; [exact Hafter|].
    match type of Hafter with ?P after => assert (Hpost : P |--
      task_create_stack_covered_success_post environment critical sg call (armv7a_irq_fiq_mask saved) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame)) end.
    { unfold task_create_stack_covered_success_post.
      Exists (armv7a_continuation_resumed_call selected call)
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
      unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_same_call,
        task_stack_call_active_key, armv7a_continuation_resumed_call, critical_region_outside.
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
      rewrite Horigin, critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
      unfold UCOS2_inv; entailer!. }
    exact (Hpost after Hafter).
Qed.
