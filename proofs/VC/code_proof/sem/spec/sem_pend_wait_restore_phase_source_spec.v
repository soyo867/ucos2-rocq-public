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

(** Physical IRQ entry writes nesting, saved SP and the parked map. Its
    projection on the original waiter's fields is obtained from those
    exact updates, including the conditional OSRunning store. *)
Lemma sem_pend_irq_deposit_wait_continuation : forall entry call sp fragments tid node eid generation,
  entry.(SchedState).(isRunning) = true ->
  entry.(TskState).(inUsedTaskStates) tid = Some node ->
  sem_pend_wait_continuation eid generation node ->
  exists current,
    (armv7a_irq_live_parked_state entry call sp fragments).(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros * Hrunning Hnode Hwait.
  destruct (sem_pend_sched_save_sp_projection entry call.(os_sched_call_stack).(stackLeaseSlot)
    sp tid node Hnode) as [current [Hcurrent Hprojection]].
  exists current; split.
  - unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    exact Hcurrent.
  - eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

(** The waiting Restore's actual MSR/IRQ/deposit/registered-trace/restore/BX
    chain supplies the exact canonical phase Ensure. The same trace carries
    wait fields and physical resources; no future ready assumption is used.
    Each additional registered client must establish its own waiter-field
    preservation. The final current test identifies this returning call. *)
Lemma sem_pend_wait_restore_irq_phase_source :
  forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg entry released node handler suspended publication
  saved cursor before original initial observed eid timeout waiting (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  sem_pend_wait_at (Some environment) critical sg original (armv7a_irq_fiq_mask saved)
    initial observed eid timeout waiting call released ->
  (forall cut state next returned previous, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) current) ->
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
  task_stack_live_coverage released.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
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
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
   UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) before ->
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
             (sem_pend_phase_restore_output
                (SemPendWaitPhase original (armv7a_irq_fiq_mask saved) initial observed eid timeout waiting)
                environment.(task_stack_call_external) environment.(task_stack_call_platform)
                (Some environment) critical sg call (armv7a_irq_fiq_mask saved) released ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg entry released node
    handler suspended publication saved cursor before original initial observed eid timeout waiting frame
    call abi parked focus payload Hwait Hwait_step Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Hextra Henter Hexit Hpublish
    Hsource Hpre written irq_input saved_heap Hprefix Hsave.
  assert (Hreleased : UCOS2_state_inv sg released).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg released) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  match type of Hpre with ?P before => assert (Hordered : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
    UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (frame)) by entailer! end.
  destruct (task_create_restore_irq_deposit environment critical arch restore sg entry released node
    handler suspended publication saved cursor before written irq_input saved_heap
    (frame)
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    Hr0 Hmask Hhandler (Hordered before Hpre) Hprefix Hsave)
    as [registry_heap [Hwritten [Hwrites [Hstores [Hbinding [Hcall [Hsaved_mask [Hvalid [Hpointer Hregistry]]]]]]]]].
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources extra_step extra_effect
    critical.(critical_region_clients) sg call suspended Hbinding Hcall Hslice Hextension Hextra Henter Hexit Hpublish
    Hsource KernelClientHeapClosed registry_heap closed_heap parked handler
    (frame)
    Hvalid Hpointer Htrace I Hregistry)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_current.
  destruct (Hreturn Hreturned_current Haddress)
    as [selected [Hpointers [Hfocus [Hlease [Hselected_sp [Hcpsr [Hregisters [Hcovered Hresume]]]]]]]].
  exists selected; split; [exact Hpointers|].
  intros irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix.
  destruct (Hresume irq_return Hrestore) as [Hmemory Howned].
  rewrite Hsaved_mask in Howned.
  assert (Hcomputed_mask : armv7a_irq_fiq_mask
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) =
    armv7a_irq_fiq_mask saved) by (rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity).
  rewrite <- Hcomputed_mask in Howned.
  match type of Howned with ?P irq_return => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (armv7a_continuation_resumed_call selected call)
      (armv7a_irq_fiq_mask
        (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     armv7a_task_stack_continuations abi
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState)
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState).(parkedTaskStacks) **
     unmap_table_rep sg ** frame))
    by entailer! end.
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call selected call) _ resume_cursor irq_return final_cursor after
    _ Hword (Hsuffix_input irq_return Howned) Hsuffix) as [Hcursor [Hafter_memory Hafter]].
  rewrite Hcomputed_mask in Hafter.
  assert (Hhistory : kernel_call_restore_history environment critical sg call released
    (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { eapply KernelCallRestoreIRQ with (extra_step := extra_step) (extra_effect := extra_effect)
      (suspended := suspended) (selected := selected) (cursor := cursor)
      (written := written) (stopped := stopped) (returned_origin := returned_origin);
      eassumption || reflexivity. }
  pose proof (kernel_call_restore_history_same_call _ _ _ _ _ _ _ Hhistory) as Hsame.
  assert (Hfields : forall previous,
    released.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    exists current,
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState).(inUsedTaskStates)
        original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) current).
  { intros previous Hprevious Hprevious_wait.
    destruct (sem_pend_irq_deposit_wait_continuation released call suspended.(armv7a_continuation_sp)
      suspended.(armv7a_continuation_fragments) original.(os_sched_call_stack).(stackLeaseSlot)
      previous eid original.(os_sched_call_stack).(stackLeaseGeneration) Hrunning Hprevious Hprevious_wait)
      as [deposited [Hdeposited Hdeposited_wait]].
    destruct (sem_pend_client_trace_preserves_wait_continuation Extra extra_effect sg
      original.(os_sched_call_stack).(stackLeaseSlot) eid original.(os_sched_call_stack).(stackLeaseGeneration)
      Hwait_step KernelClientHeapClosed parked KernelClientHeapClosed returned deposited Hstates Hvalid
      Hdeposited Hdeposited_wait) as [_ [current [Hwait_current Hcurrent_wait]]].
    exists current; split; assumption. }
  pose proof (sem_pend_wait_at_restore_source environment critical sg original (armv7a_irq_fiq_mask saved)
    initial observed eid timeout waiting call released (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) Hwait Hhistory Hfields)
    as Hwait_after.
  assert (Hpreserved : task_tcb_init_stack_return_preserved call released
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { eapply task_tcb_init_stack_irq_return_preserved; try eassumption.
    rewrite <- Hnormal; exact Hsources. }
  assert (Hsource_preserved : UCOS2_state_inv sg released -> kernel_call_task_source call released ->
    kernel_call_task_source (armv7a_continuation_resumed_call selected call)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { intros Hreleased_valid Hcall_source.
    unfold armv7a_continuation_resumed_call, kernel_call_task_source;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    rewrite Hlease; exact (proj2 (proj2 Hpreserved) Hcall_source). }
  split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - unfold armv7a_continuation_resumed_call in Hhistory, Hsame, Hsource_preserved, Hwait_after.
    rewrite Hlease, Horigin in Hhistory, Hsame, Hsource_preserved, Hwait_after.
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
    { unfold sem_pend_phase_restore_output.
      Exists (armv7a_continuation_resumed_call selected call)
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
      unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
        sem_pend_restore_phase_pre, sem_pend_optional_stack_resources, task_tcb_init_stack_capsules.
      rewrite mutex_query_closed_equiv.
      unfold kernel_call_execution_owned, task_stack_call_active_key, armv7a_continuation_resumed_call.
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
      rewrite Hlease, Horigin; unfold UCOS2_inv; entailer!; try discriminate. }
    exact (Hpost after Hafter).
Qed.
