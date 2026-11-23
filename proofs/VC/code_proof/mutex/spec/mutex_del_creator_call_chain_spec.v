Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_type_loan_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_call_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One real producer/consumer chain, rather than assuming a Type loan at
    a future handler heap. The interrupted creator's actual DSB/MSR and
    IRQ save supply the frame/map deposit; deterministic counter/SP writes
    identify the supplied handler heap. Registered SOURCE steps, including
    another Sem/Mbox allocation and completed publication, transport that
    pending ECB to the actual selected heap.

    The selected transfer's hooked state must be this produced state; the
    destination/port-layout facts belong to the actual downstream scheduler
    cut. They are not promised at the creator's entry. The taken descriptor
    is existentially produced by install/take, and the later indexed IRQ
    relation must identify THAT descriptor with the earlier Del Save.

    This does not classify an arbitrary BSP handler or prove its return,
    a scheduling hook, or the public Save call. It supplies the particular
    source/heap composition those owners must consume, with no new ABI law. *)
Lemma mutex_del_creator_release_clients_selected_type :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    (register_source : Armv7aIRQRegisterSave external platform port continuations)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg creator creator_call creator_saved acquired state pointer observer allocation observed
    handler saved node publication restore_entry cursor before written_cursor released saved_heap
    handler_heap selected_heap cpu_sr (frame : Assertion),
  mutex_del_creator_arguments creator -> pointer = event_pool_addr sg observer ->
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some observed ->
  cursor.(kernel_restore_r0) = creator_saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_call) = creator_call ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask creator_saved ->
  handler.(os_int_exit_interrupted_pc) = restore_entry + 8 ->
  mutex_del_creator_irq_input sg state handler saved node publication ->
  (critical_region_masked platform critical sg creator_call.(os_sched_call_invocation)
      creator_call.(os_sched_call_origin) creator_saved acquired **
    os_sched_context_resources external creator_call **
    mutex_del_creator_heap_resources continuations sg pointer state **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    ((cpu_sr # UInt |->_) ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  armv7a_save_transition continuations handler saved released saved_heap ->
  kernel_heap_execution
    (armv7a_irq_live_entry_writes sg state creator_call.(os_sched_call_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_sp)) saved_heap handler_heap ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg
    KernelClientHeapClosed handler_heap KernelClientHeapClosed selected_heap ->
  exists returned,
    written_cursor = kernel_restore_write_cpsr cursor /\
    saved.(armv7a_continuation_call) = Some creator_call /\
    saved.(armv7a_continuation_pc) = restore_entry + 8 /\
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      released.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg
      KernelClientHeapClosed
      (armv7a_irq_live_parked_state state creator_call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) KernelClientHeapClosed returned /\
    (forall transfer original return_pc,
      transfer.(os_int_exit_hooked_state) = returned ->
      os_int_exit_destination_binding external transfer ->
      tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) TCBStkPtr =
        task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
      exists installed selected,
        sched_install_heap_fragment sg selected_heap installed
          (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
          transfer.(os_int_exit_incoming_sp) /\
        armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
        (forall registers earlier_handler earlier_before earlier_after restored final_registers
          selected_state masked_heap after,
          valid_os_cpu_sr registers.(kernel_save_cpsr) ->
          registers.(kernel_save_lr) = return_pc ->
          earlier_handler.(os_int_exit_interrupted_call) = original ->
          earlier_handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
          earlier_handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
          armv7a_irq_register_save register_source registers.(kernel_save_cpsr) registers.(kernel_save_lr)
            earlier_handler selected earlier_before earlier_after ->
          armv7a_continuation_restore_reads selected installed ->
          armv7a_restore_transition continuations handler selected installed restored ->
          armv7a_save_suffix_transition suffix (mutex_del_irq_restored_registers selected)
            (os_int_exit_installed_state transfer) restored final_registers selected_state masked_heap ->
          kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) masked_heap after ->
          selected_state = os_int_exit_installed_state transfer /\
          final_registers.(kernel_save_return_word) = Some return_pc /\
          final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
          uchar_load pointer observed after /\
          (critical_region_masked platform critical sg original.(os_sched_call_invocation)
              original.(os_sched_call_origin) final_registers.(kernel_save_r0) selected_state **
            os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
            mutex_del_creator_heap_resources continuations sg pointer selected_state **
            (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
            task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
            frame) after)).
Proof.
  intros external platform port critical arch continuations restore register_source suffix sg creator creator_call
    creator_saved acquired state pointer observer allocation observed handler saved node publication restore_entry
    cursor before written_cursor released saved_heap handler_heap selected_heap cpu_sr frame Hargs Hpointer Hget Htype
    Hr0 Hmask Hcall Hhandler_mask Hpc Hinput Hpre Hprefix Hsave Hdeposit Hclients.
  destruct (mutex_del_creator_release_irq_deposit external platform port critical arch continuations restore
    sg creator_call creator_saved acquired state pointer handler saved node publication restore_entry cursor
    before written_cursor released saved_heap ((cpu_sr # UInt |->_) ** frame)
    Hr0 Hmask Hcall Hhandler_mask Hpc Hinput Hpre Hprefix Hsave)
    as [produced [Hwritten [Hsaved_call [Hsaved_pc [Hwrites [Hentry Hhandler]]]]]].
  assert (produced = handler_heap) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (parked := armv7a_irq_live_parked_state state creator_call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments)) in *.
  assert (Hget_parked : parked.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation).
  { destruct Hinput as [Hrunning _].
    unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp,
      armv7a_irq_entry_counter_state; rewrite Hrunning; exact Hget. }
  assert (Hopen : mutex_del_creator_heap_resources continuations sg pointer parked **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** ((cpu_sr # UInt |->_) ** frame)) |--
    kernel_client_heap_resources continuations (mutex_del_creator_pending continuations) sg
      KernelClientHeapClosed parked **
      (event_private_storage_rep sg observer allocation **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** (cpu_sr # UInt |->_) ** frame))).
  { sep_apply_l_atomic (proj1 (mutex_del_creator_heap_resources_equiv_private_storage external platform port
      continuations sg pointer parked observer allocation Hpointer Hget_parked)).
    cbn [kernel_client_heap_resources]; entailer!. }
  destruct (mutex_del_creator_publication_trace_type external platform port continuations creator sg pointer
    KernelClientHeapClosed parked handler_heap selected_heap observer allocation observed
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** (cpu_sr # UInt |->_) ** frame)
    Hargs Hpointer Hget_parked Htype Hclients (Hopen handler_heap Hhandler))
    as [returned [Hlogical Hloan]].
  exists returned; split; [exact Hwritten|]. split; [exact Hsaved_call|]. split; [exact Hsaved_pc|].
  split; [exact Hwrites|]. split; [exact Hlogical|].
  intros transfer original return_pc Hreturned Hdestination Haddress.
  rewrite <- Hreturned in Hloan.
  exact (mutex_del_private_selected_save_type external platform port critical arch continuations
    register_source suffix sg handler original transfer return_pc pointer observed cpu_sr frame selected_heap
    Hdestination Haddress Hloan).
Qed.
