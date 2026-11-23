Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_irq_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_return_restore_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_return_source_spec.
Import Monad MonadNotation.
Local Open Scope monad_scope.

(** Consume the exact cleanup checkpoint produced by the waiting return
    source. Its result and saved-mask observations stay historical, while
    the actual indexed IRQ deposit/registered trace/frame restore/BX
    produces the current returned resources. No wait-field preservation is
    needed after this completed checkpoint; no balanced generic trace is
    asserted. The family restrictions are those of the adopted producer. *)
Lemma sem_pend_checkpoint_irq_public_return_source :
  forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg entry released node handler suspended publication
  saved cursor before (frame : Assertion) original mask initial pevent timeout eid error perr X,
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  sem_pend_checkpoint_result (Some environment) critical sg original pevent timeout initial error released ->
  pevent <> 0 -> pevent = event_addr sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  kernel_stack_call_same_call call original -> interrupt_saved_value mask saved ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
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
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) suspended.(armv7a_continuation_sp) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients) (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None extra_effect ->
  (task_tcb_init_stack_restore_input environment critical sg call saved entry released **
   unmap_table_rep sg ** perr # UChar |-> error **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) before ->
  forall written irq_input saved_heap,
  armv7a_restore_prefix_transition restore cursor before written irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  exists registry_heap,
    written = kernel_restore_write_cpsr cursor /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended) irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin) parked stopped returned_origin returned /\
        (stopped = false ->
         returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
         exists selected,
           armv7a_irq_restore_pointer_reads sg closed_heap
             (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
           (forall irq_return resume_cursor final_cursor after,
             armv7a_restore_transition abi handler selected closed_heap irq_return ->
             resume_cursor.(kernel_restore_msr_word) = Some
               (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) ->
             resume_cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
             armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
             final_cursor.(kernel_restore_return_word) = Some selected.(armv7a_continuation_lr) /\
             (sem_pend_stack_call_post environment.(task_stack_call_external)
                environment.(task_stack_call_platform) (Some environment) critical sg original mask
                pevent timeout perr initial X **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                handler.(os_int_exit_handler_fragments) ** frame) after))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg entry released node
    handler suspended publication saved cursor before frame original mask initial pevent timeout eid error perr X
    call abi parked focus payload Hcheckpoint Hnonnull Haddress_event Hordered Hsame Hsaved Hexec
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp
    Hr0 Hmask Hhandler Hextension Hextra Henter Hexit Hpublish Hsource Hpre written irq_input saved_heap Hprefix Hsave.
  assert (Hactive : task_stack_call_active_key call = Some (task_stack_key call.(os_sched_call_stack))).
  { unfold task_stack_call_active_key; rewrite Horigin; reflexivity. }
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage released.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
     UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     (perr # UChar |-> error ** frame))) end.
  { unfold task_tcb_init_stack_restore_input, task_tcb_init_stack_capsules,
      task_tcb_init_stack_covered_capsules, task_tcb_init_stack_context; rewrite Hactive; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Hsource_pre].
  destruct (sem_pend_return_restore_irq_phase_source environment critical arch Extra restore
    extra_resources extra_step extra_effect sg entry released node handler suspended publication saved cursor before
    (perr # UChar |-> error ** frame) Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Hextra Henter Hexit Hpublish
    Hsource Hsource_pre written irq_input saved_heap Hprefix Hsave)
    as [registry_heap [Hwritten [Hwrites [Hdeposit Htrace]]]].
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hdeposit|].
  intros closed_heap Hclosed.
  destruct (Htrace closed_heap Hclosed) as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hcurrent_returned.
  destruct (Hreturn Hnormal Hcurrent_returned) as [selected [Hpointer Hrestore]].
  exists selected; split; [exact Hpointer|].
  intros irq_return resume_cursor final_cursor after Hirq Hword Hlr Hsuffix.
  destruct (Hrestore irq_return resume_cursor final_cursor after Hirq Hword Hlr Hsuffix) as [Hbranch Hafter].
  split; [exact Hbranch|].
  fold call in Hafter.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { rewrite <- sem_pend_phase_restore_return_output, (proj2 Hsaved).
    match goal with |- ?P |-- _ => assert (Hpad : P |--
      (TT ** sem_pend_stack_restore_source_output environment.(task_stack_call_external)
        environment.(task_stack_call_platform) (Some environment) critical sg call mask released **
        unmap_table_rep sg ** perr # UChar |-> error) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
      by (entailer!; apply derivable1_truep_intros) end.
    eapply derivable1_trans; [exact Hpad|].
    sep_apply_l_atomic (sem_pend_stack_call_post_from_restore environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (Some environment) critical sg original call mask pevent timeout perr
      initial released error eid X Hcheckpoint Hnonnull Haddress_event Hordered Hsame Hexec); entailer!. }
  exact (Hfinish after Hafter).
Qed.
