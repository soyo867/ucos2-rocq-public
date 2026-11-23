Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_type_loan_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** _6's private branch at the real selected-return cut. The creator's
    Type loan is an INPUT on the actual handler heap, not inferred from
    program_inv or smuggled through an unknown open Restore. The adopted
    generic full-map Save consumer is reused directly from its existing
    Task owner; its statement contains no TaskCreate/TCBInit arguments.

    The selected descriptor is produced by the actual install/take. Only
    when that SAME descriptor has the supplied indexed earlier IRQ-save
    source do the observations identify this Del's MRS value and caller
    LR. No descriptor is selected to make those equalities true.

    The following masked instructions cannot execute intervening C. They
    transport the actual Type/private-image owner, table, whole map and
    handler fragments to cpu_sr's real store and the protected Type load.
    Producing the initial handler cut through all prior clients/switches
    remains separate; this is not a complete public Save/Del contract. *)
Lemma mutex_del_private_selected_save_type :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (register_source : Armv7aIRQRegisterSave external platform port continuations)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg handler original transfer return_pc pointer observed cpu_sr (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (pointer # UChar |-> observed **
   mutex_del_creator_type_residual continuations sg pointer transfer.(os_int_exit_hooked_state) observed **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** (cpu_sr # UInt |->_) ** frame)) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    armv7a_continuation_binding saved /\
    saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    (forall registers earlier_handler earlier_before earlier_after restored final_registers acquired saved_heap after,
      valid_os_cpu_sr registers.(kernel_save_cpsr) ->
      registers.(kernel_save_lr) = return_pc ->
      earlier_handler.(os_int_exit_interrupted_call) = original ->
      earlier_handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
      earlier_handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
      armv7a_irq_register_save register_source registers.(kernel_save_cpsr) registers.(kernel_save_lr)
        earlier_handler saved earlier_before earlier_after ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      armv7a_save_suffix_transition suffix (mutex_del_irq_restored_registers saved)
        (os_int_exit_installed_state transfer) restored final_registers acquired saved_heap ->
      kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) saved_heap after ->
      acquired = os_int_exit_installed_state transfer /\
      final_registers.(kernel_save_return_word) = Some return_pc /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
      uchar_load pointer observed after /\
      (critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       mutex_del_creator_heap_resources continuations sg pointer acquired **
       (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       frame) after).
Proof.
  intros external platform port critical arch continuations register_source suffix sg handler original transfer
    return_pc pointer observed cpu_sr frame heap Hdestination Haddress Hpre.
  assert (Hopen : pointer # UChar |-> observed **
      mutex_del_creator_type_residual continuations sg pointer transfer.(os_int_exit_hooked_state) observed **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (cpu_sr # UInt |->_) ** frame) |--
    EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      transfer.(os_int_exit_hooked_state).(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateStorage) EventTypeField = Some observed) &&
    (UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
      armv7a_task_continuations continuations transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler **
       (unmap_table_rep sg ** event_private_storage_rep sg eid allocation ** (cpu_sr # UInt |->_) ** frame)))).
  { unfold mutex_del_creator_type_residual; Intros eid allocation.
    assert (Hbindings : pointer = event_pool_addr sg eid /\
      transfer.(os_int_exit_hooked_state).(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateStorage) EventTypeField = Some observed) by tauto.
    destruct Hbindings as [Hpointer [Hget Htype]].
    Exists eid allocation.
    rewrite Hpointer; sep_apply_l_atomic (event_private_storage_rep_merge_type sg eid allocation observed Htype).
    unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen heap Hpre) as [eid [allocation [[Hpointer [Hget Htype]] Hopened]]].
  destruct (task_tcb_init_selected_save_resources external platform port critical arch continuations suffix
    sg handler original transfer return_pc _ heap Hdestination Haddress Hopened)
    as [installed [saved [Hinstall [Hbinding [Hstack Hresume]]]]].
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hbinding|]. split; [exact Hstack|].
  intros registers earlier_handler earlier_before earlier_after restored final_registers acquired saved_heap after
    Hvalid Hlr Hearlier_call Hearlier_pc Hearlier_mask Hearlier_save Hreads Hrestore Hsuffix Hstore.
  destruct (armv7a_irq_register_save_refinement _ _ _ _ register_source _ _ _ _ _ _ Hearlier_save)
    as [Hsave [Hsaved_r0 Hsaved_lr]].
  destruct (armv7a_save_transition_observations _ _ _ continuations _ _ _ _ Hsave)
    as [_ [Hsaved_call [_ [Hsaved_mask [Hsaved_pc _]]]]].
  rewrite Hearlier_call in Hsaved_call; rewrite Hearlier_pc in Hsaved_pc.
  assert (Hsaved_value : interrupt_saved_value
    (armv7a_irq_fiq_mask (mutex_del_irq_restored_registers saved).(kernel_save_cpsr))
    (mutex_del_irq_restored_registers saved).(kernel_save_r0)).
  { cbn [mutex_del_irq_restored_registers kernel_save_cpsr kernel_save_r0].
    rewrite Hsaved_r0, Hsaved_mask, Hearlier_mask; split; [exact Hvalid|reflexivity]. }
  destruct (Hresume (mutex_del_irq_restored_registers saved) restored final_registers acquired saved_heap
    Hsaved_call Hsaved_pc ltac:(congruence) eq_refl eq_refl eq_refl Hsaved_value Hreads Hrestore Hsuffix)
    as [Hacquired [Hreturn [Hvalue Hsaved]]].
  assert (Hresult : final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr)).
  { rewrite Hvalue; exact Hsaved_r0. }
  assert (Hmasked : critical_region_masked platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
      os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
      UCOS2_inv sg acquired ** armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
      (unmap_table_rep sg ** event_private_storage_rep sg eid allocation ** (cpu_sr # UInt |->_) ** frame) |--
    mutex_del_call_masked external platform critical sg (armv7a_continuation_resumed_call saved original)
      final_registers.(kernel_save_r0) acquired acquired ** (cpu_sr # UInt |->_) **
      (armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) **
       event_private_storage_rep sg eid allocation **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)).
  { unfold mutex_del_call_masked; rewrite kernel_program_inv_split_unmap.
    cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
  pose proof (mutex_del_call_saved_return_store external platform critical sg
    (armv7a_continuation_resumed_call saved original) final_registers.(kernel_save_r0) acquired acquired
    cpu_sr saved_heap after _ ltac:(rewrite Hresult; exact Hvalid) (Hmasked saved_heap Hsaved) Hstore) as Hbody.
  assert (Hget_acquired : acquired.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation).
  { rewrite Hacquired; exact Hget. }
  assert (Hloan : mutex_del_call_masked external platform critical sg
      (armv7a_continuation_resumed_call saved original) final_registers.(kernel_save_r0) acquired acquired **
      (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) **
       event_private_storage_rep sg eid allocation **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) |--
    pointer # UChar |-> observed ** mutex_del_creator_type_residual continuations sg pointer acquired observed **
      (critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)).
  { unfold mutex_del_call_masked.
    sep_apply_l_atomic (event_private_storage_rep_split_type sg eid allocation observed Htype).
    unfold mutex_del_creator_type_residual; Exists eid allocation.
    unfold kernel_client_heap_world.
    cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin].
    rewrite Hpointer; entailer!. }
  destruct (mutex_del_creator_type_load_return external platform port continuations sg pointer acquired observed
    after _ (Hloan after Hbody)) as [Hload Hreturned].
  split; [exact Hacquired|]. split; [exact Hreturn|]. split; [exact Hresult|]. split; [exact Hload|].
  match type of Hreturned with ?P after => assert (Hclose : P |--
    critical_region_masked platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
    os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
    mutex_del_creator_heap_resources continuations sg pointer acquired **
    (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
  end.
  { entailer!. }
  exact (Hclose after Hreturned).
Qed.
