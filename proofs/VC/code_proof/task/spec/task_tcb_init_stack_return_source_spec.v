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

(** The three actual state edges are retained: deposit, registered handler
    execution, and take. Only their needed observations compose; no flat
    source trace across deposit/take is postulated. *)
Lemma task_tcb_init_stack_irq_return_preserved :
  forall environment critical sg call released node sp fragments returned returned_origin,
  let parked := armv7a_irq_live_parked_state released call sp fragments in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(SchedState).(isRunning) = true ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  UCOS2_state_inv sg parked ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) parked false returned_origin returned ->
  returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  task_tcb_init_stack_return_preserved call released
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
Proof.
  intros environment critical sg call released node sp fragments returned returned_origin parked
    Horigin Hrunning Hnode Hvalid Htrace Hcurrent.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg call.(os_sched_call_invocation)
    parked returned Hinterval Hvalid) as [_ [Hframe Hactive]].
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask released.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node sp))
    (task_stack_park_fragments released.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) fragments)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hlive : task_invocation_active released.(TskState) call.(os_sched_call_invocation)
    call.(os_sched_call_origin) ->
    task_invocation_active returned.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { intro Hbefore; apply Hactive; rewrite Htasks.
    change (task_invocation_active
      (glob_task_set_usedtask released.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp node sp)) call.(os_sched_call_invocation) call.(os_sched_call_origin)).
    eapply task_set_saved_sp_preserves_invocation_active; eassumption. }
  split.
  - unfold task_creation_frame in *; rewrite Htasks in Hframe.
    exact Hframe.
  - split; [exact Hlive|].
    intros [Hcall_origin [Hbefore Hcall_current]].
    split; [exact Hcall_origin|]. split; [apply Hlive; exact Hbefore|].
    unfold task_execution_current; rewrite Horigin; exact Hcurrent.
Qed.

(** Both successful publication and no-free return consume the same actual
    MSR/IRQ/registry/restore/BX chain. [result] and [released] are the already
    established TCBInit result history; a failed call keeps its actual
    initialized private buffer through that entire chain. The stop/current
    tests classify the observed normal return. No eventual return or ready
    ordering is required by the public contract. *)
Lemma task_tcb_init_stack_restore_irq_call_post :
  forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg entry released node handler suspended publication
  saved cursor before region args task_return lower upper initial_name initial result (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    call.(os_sched_call_invocation) call.(os_sched_call_origin) initial result released ->
  task_tcb_init_stack_source_preserved call initial released ->
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
   task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame) before ->
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
             (task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
                call.(os_sched_call_invocation) call.(os_sched_call_origin)
                (armv7a_irq_fiq_mask saved) initial call result ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg entry released node
    handler suspended publication saved cursor before region args task_return lower upper initial_name initial result frame
    call abi parked focus payload Hresult Hsource_before Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
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
    (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)) by entailer! end.
  destruct (task_create_restore_irq_deposit environment critical arch restore sg entry released node
    handler suspended publication saved cursor before written irq_input saved_heap
    (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    Hr0 Hmask Hhandler (Hordered before Hpre) Hprefix Hsave)
    as [registry_heap [Hwritten [Hwrites [Hstores [Hbinding [Hcall [Hsaved_mask [Hvalid [Hpointer Hregistry]]]]]]]]].
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources extra_step extra_effect
    critical.(critical_region_clients) sg call suspended Hbinding Hcall Hslice Hextension Hextra Henter Hexit Hpublish
    Hsource KernelClientHeapClosed registry_heap closed_heap parked handler
    (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)
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
     unmap_table_rep sg ** task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame))
    by entailer! end.
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call selected call) _ resume_cursor irq_return final_cursor after
    _ Hword (Hsuffix_input irq_return Howned) Hsuffix) as [Hcursor [Hafter_memory Hafter]].
  rewrite Hcomputed_mask in Hafter.
  assert (Hpreserved : task_tcb_init_stack_return_preserved call released
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { eapply task_tcb_init_stack_irq_return_preserved; try eassumption.
    rewrite <- Hnormal; exact Hsources. }
  split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
    { unfold task_tcb_init_stack_call_post; Exists released.
      unfold task_tcb_init_stack_call_return_post.
      Exists (armv7a_continuation_resumed_call selected call)
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
      unfold task_tcb_init_stack_save_input, task_tcb_init_stack_capsules,
        task_tcb_init_stack_same_call, task_stack_call_active_key,
        armv7a_continuation_resumed_call, critical_region_outside.
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
      rewrite Hlease, Horigin, critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
      unfold UCOS2_inv; entailer!; rewrite <- Horigin; exact Hresult. }
    exact (Hpost after Hafter).
Qed.
