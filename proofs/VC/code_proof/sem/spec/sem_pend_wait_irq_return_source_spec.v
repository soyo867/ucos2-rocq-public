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
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_resume_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_restore_phase_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.

Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_save_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Import Monad MonadNotation.
Local Open Scope monad_scope.

(** The actual second-Save MRS/IRQ producer is consumed on its returned
    heap by all three result branches and the common cleanup. The exact
    cleanup checkpoint and Restore input remain exposed for final IRQ
    consumers, while the actual uninterrupted MSR/BX gives the public post.
    Registered extension preservation and this no-selection family's
    current-return guards are inherited unchanged from the source theorem. *)
Lemma sem_pend_wait_irq_public_return_source :
  forall environment critical arch Extra
  (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  extra_resources extra_step extra_effect sg entry node handler suspended publication
  registers after_mrs before irq_input saved_heap original initial observed eid timeout waiting (frame : Assertion) pevent perr X,
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state entry call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  sem_pend_wait_selected_at (Some environment) critical sg original (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    initial observed eid timeout waiting call entry ->
  (forall cut state next returned previous, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) current) ->
  (forall cut state next returned previous, extra_effect sg cut state next returned ->
    sem_pend_resume_entry sg state eid original.(os_sched_call_stack).(stackLeaseSlot) previous ->
    exists current, sem_pend_resume_entry sg returned eid original.(os_sched_call_stack).(stackLeaseSlot) current) ->
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
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
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) suspended.(armv7a_continuation_sp) ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers entry before after_mrs entry irq_input ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
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
  (task_tcb_init_stack_save_input environment critical sg call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) entry ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** (perr # UChar |->_ ** frame)) irq_input ->
  armv7a_irq_register_save registers_source after_mrs.(kernel_save_r0) after_mrs.(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  exists registry_heap,
    nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr) /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
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
           (forall restored cursor final_registers acquired acquired_heap,
             armv7a_restore_transition abi handler selected closed_heap restored ->
             cursor.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
             cursor.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
             cursor.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
             armv7a_save_suffix_transition suffix cursor
               (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
               final_registers acquired acquired_heap ->
             kernel_save_after_mrs_execution arch cursor
               (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
               final_registers acquired acquired_heap /\
             final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
             final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
             exists cleanup_call resumed resume_node cleaning clean_node branch_heap cleaned,
                 sem_pend_resume_branch_fragment sg resumed eid original.(os_sched_call_stack).(stackLeaseSlot) resume_node acquired_heap branch_heap /\
                 sem_pend_cleanup_fragment sg perr
                   (encode_os_err_code (sem_pend_resume_error (encode_pend_status resume_node.(statPend)))) branch_heap cleaned /\
                 sem_pend_checkpoint_result (Some environment) critical sg original pevent timeout initial
                   (encode_os_err_code (sem_pend_resume_error (encode_pend_status resume_node.(statPend))))
                   (event_pend_cleanup_state sg false cleaning original.(os_sched_call_stack).(stackLeaseSlot) clean_node) /\
                 kernel_stack_call_same_call cleanup_call original /\ interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) /\
                 (task_tcb_init_stack_restore_input environment critical sg cleanup_call final_registers.(kernel_save_r0) resumed
                   (event_pend_cleanup_state sg false cleaning original.(os_sched_call_stack).(stackLeaseSlot) clean_node) **
                   unmap_table_rep sg ** perr # UChar |->
                     encode_os_err_code (sem_pend_resume_error (encode_pend_status resume_node.(statPend))) ** (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) cleaned /\
                 (forall cursor written middle final_cursor after,
                   cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
                   armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
                   armv7a_restore_prefix_transition restore cursor cleaned written middle ->
                   armv7a_restore_suffix_transition restore written middle final_cursor after ->
                   kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
                   (sem_pend_stack_call_post environment.(task_stack_call_external)
                     environment.(task_stack_call_platform) (Some environment) critical sg original (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
                     pevent timeout perr initial X ** (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) after)))).

Proof.
  intros environment critical arch Extra suffix restore registers_source extra_resources extra_step extra_effect
    sg entry node handler suspended publication registers after_mrs before irq_input saved_heap original initial observed
    eid timeout waiting frame pevent perr X call abi parked focus payload Hnonnull Haddress_event Heid Hslot Hlayout
    Hordered Hexec Hselected_wait Hwait_step Hresume_step Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hregister_valid Hmrs Hpc Hhandler
    Hextension Hextra Henter Hexit Hpublish Hsource Hpre Hcapture.
  destruct (sem_pend_wait_mrs_irq_save_phase_source environment critical arch Extra suffix registers_source
    extra_resources extra_step extra_effect sg entry node handler suspended publication registers after_mrs before
    irq_input saved_heap original initial observed eid timeout waiting (perr # UChar |->_ ** frame)
    Hselected_wait Hwait_step Hresume_step Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hregister_valid Hmrs Hpc Hhandler Hextension Hextra Henter Hexit Hpublish
    Hsource Hpre Hcapture) as [registry_heap [Horiginal [Hwrites [Hdeposit Htrace]]]].
  exists registry_heap; split; [exact Horiginal|]. split; [exact Hwrites|]. split; [exact Hdeposit|].
  intros closed_heap Hclosed.
  destruct (Htrace closed_heap Hclosed) as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hcurrent_returned.
  destruct (Hreturn Hnormal Hcurrent_returned) as [selected [Hpointer Hsave]].
  exists selected; split; [exact Hpointer|].
  intros restored cursor final_registers acquired acquired_heap Hrestore Hcpsr Hr0 Hlr Hsuffix.
  destruct (Hsave restored cursor final_registers acquired acquired_heap Hrestore Hcpsr Hr0 Hlr Hsuffix)
    as [Hrun [Horiginal_return [Hbranch Hphase]]].
  split; [exact Hrun|]. split; [exact Horiginal_return|]. split; [exact Hbranch|].
  fold call in Hphase.
  eapply (sem_pend_saved_wait_return_source environment critical arch restore sg original
    (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) initial observed eid pevent timeout waiting call entry
    final_registers.(kernel_save_r0) perr
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
    acquired_heap X Hnonnull Haddress_event Heid Hslot Hlayout Hordered Hexec).
  match type of Hphase with ?P acquired_heap => match goal with |- ?Q acquired_heap =>
    assert (Hreorder : P |-- Q) by entailer! end end.
  exact (Hreorder acquired_heap Hphase).
Qed.
