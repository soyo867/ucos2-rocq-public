Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A proved specialization of the EXISTING ABI, not a new ABI law.
    The descriptor is the one supplied by the actual save transition.
    Its equality index is stored with that same linear dormant resource.
    Only this particular save is represented by the specialized relation;
    its actual execution is not altered or assumed to terminate. Restore
    uses the original transition verbatim. Other stack keys already have
    [emp] rights in a focused world and gain no resources from this index. *)
Definition mutex_del_retained_continuation_abi external platform port
  (abi : Armv7aContinuationABI external platform port) (deposited : Armv7aContinuation)
  : Armv7aContinuationABI external platform port.
Proof.
  refine {| armv7a_dormant_continuation := fun saved =>
      coq_prop (saved = deposited) && armv7a_dormant_continuation abi saved;
    armv7a_initial_execution := armv7a_initial_execution abi;
    armv7a_save_transition := fun context saved before after =>
      saved = deposited /\ armv7a_save_transition abi context saved before after;
    armv7a_restore_transition := armv7a_restore_transition abi |}.
  - intros context saved before after [Hsame Hrun].
    exact (armv7a_save_transition_observations _ _ _ abi context saved before after Hrun).
  - intros context saved call frame before after Hcall Hcontext Hbinding Hmask Hpc Hsp Hfragments
      Hpre [Hsame Hrun].
    destruct (armv7a_save_transition_resources _ _ _ abi context saved call frame before after
      Hcall Hcontext Hbinding Hmask Hpc Hsp Hfragments Hpre Hrun) as [Hwrites Hpost].
    split; [exact Hwrites|].
    assert (Hindex : interrupt_platform_running platform context.(os_int_exit_invocation)
        context.(os_int_exit_origin) 192 ** os_int_exit_context_resources port context **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved ** frame |--
      interrupt_platform_running platform context.(os_int_exit_invocation)
        context.(os_int_exit_origin) 192 ** os_int_exit_context_resources port context **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (coq_prop (saved = deposited) && armv7a_dormant_continuation abi saved) ** frame) by entailer!.
    exact (Hindex after Hpost).
  - intros context saved frame before after Hreads Hpre Hrun.
    assert (Herase : interrupt_platform_running platform context.(os_int_exit_invocation)
        context.(os_int_exit_origin) 192 ** os_int_exit_context_resources port context **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (coq_prop (saved = deposited) && armv7a_dormant_continuation abi saved) ** frame |--
      interrupt_platform_running platform context.(os_int_exit_invocation)
        context.(os_int_exit_origin) 192 ** os_int_exit_context_resources port context **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved ** frame) by entailer!.
    exact (armv7a_restore_transition_resources _ _ _ abi context saved frame before after
      Hreads (Herase before Hpre) Hrun).
Defined.

Lemma mutex_del_save_retains_actual_descriptor : forall external platform port
  (abi : Armv7aContinuationABI external platform port) context deposited before after,
  armv7a_save_transition abi context deposited before after ->
  armv7a_save_transition (mutex_del_retained_continuation_abi external platform port abi deposited)
    context deposited before after.
Proof. intros; split; [reflexivity|exact H]. Qed.

Lemma mutex_del_retained_foreign_entry_eq : forall external platform port
  (abi : Armv7aContinuationABI external platform port) deposited focus key payload,
  key <> armv7a_call_focus_key focus ->
  armv7a_parked_continuation_entry
    (mutex_del_retained_continuation_abi external platform port abi deposited) focus key payload =
  armv7a_parked_continuation_entry abi focus key payload.
Proof.
  intros; unfold armv7a_parked_continuation_entry.
  destruct task_stack_key_eq_dec; [contradiction|reflexivity].
Qed.

(** The old physical world actually supplies this input. Only an ABSENT
    focus is indexed before the save; all nonfocused rights are the same
    [emp] as before and all foreign stack bytes remain in program ownership.
    No inhabited whole-map conversion or foreign dormant capability is
    assumed. This condition is already the real first-save entry condition. *)
Lemma mutex_del_retained_world_before_save : forall external platform port
  (abi : Armv7aContinuationABI external platform port) deposited focus sg state,
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = None ->
  armv7a_continuation_world abi focus (kernel_program_inv sg) state |--
  armv7a_continuation_world
    (mutex_del_retained_continuation_abi external platform port abi deposited)
    focus (kernel_program_inv sg) state.
Proof.
  intros external platform port abi deposited focus sg state Hnone.
  rewrite !kernel_program_continuation_world_split_unmap.
  unfold armv7a_continuation_world at 1.
  sep_apply_l_atomic (armv7a_parked_focus_absent_emp external platform port abi focus _ Hnone).
  sep_apply_l_atomic (armv7a_continuation_world_open_absent external platform port
    (mutex_del_retained_continuation_abi external platform port abi deposited) focus sg state Hnone).
  entailer!.
Qed.

(** Actual source producer. The original ABI's real save creates the one
    dormant capability; the actual counter/SP writes put it in the focused
    map with its precise descriptor index. Indexing is NOT a new input. *)
Lemma mutex_del_irq_source_deposits_retained_descriptor : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler deposited publication (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc) deposited.(armv7a_continuation_lr) in
  let retained := mutex_del_retained_continuation_abi external platform port abi deposited in
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
    deposited.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) deposited.(armv7a_continuation_sp) ->
  (os_int_exit_frame_save_pre external platform handler **
    (armv7a_continuation_world abi focus (kernel_program_inv sg) entry ** frame)) before ->
  armv7a_save_transition abi handler deposited before saved_heap ->
  exists final,
    deposited.(armv7a_continuation_call) = Some call /\
    deposited.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    armv7a_irq_fiq_mask deposited.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
    kernel_heap_writes (armv7a_continuation_save_writes deposited)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot)
        deposited.(armv7a_continuation_sp)) saved_heap final /\
    (armv7a_continuation_world retained focus (kernel_program_inv sg)
       (armv7a_irq_live_parked_state entry call deposited.(armv7a_continuation_sp)
         deposited.(armv7a_continuation_fragments)) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler deposited publication frame before saved_heap
    call focus retained Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication
    Hsp Hpre Hsave.
  assert (Hindex : os_int_exit_frame_save_pre external platform handler **
      (armv7a_continuation_world abi focus (kernel_program_inv sg) entry ** frame) |--
    os_int_exit_frame_save_pre external platform handler **
      (armv7a_continuation_world retained focus (kernel_program_inv sg) entry ** frame)).
  { sep_apply_l_atomic (mutex_del_retained_world_before_save external platform port abi deposited focus sg entry Hnone).
    entailer!. }
  pose proof (mutex_del_save_retains_actual_descriptor external platform port abi handler deposited
    before saved_heap Hsave) as Hindexed_save.
  destruct (kernel_program_irq_source_save_deposit external platform port retained sg entry node handler
    deposited publication frame before saved_heap Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp (Hindex before Hpre) Hindexed_save)
    as [final [Hcall [Hpc [Hwrites [Hentry Hpost]]]]].
  destruct (armv7a_save_transition_observations _ _ _ abi handler deposited before saved_heap Hsave)
    as [_ [_ [_ [Hmask _]]]].
  exists final; split; [exact Hcall|]. split; [exact Hpc|]. split; [exact Hmask|].
  split; [exact Hwrites|]. split; assumption.
Qed.

(** Taking this focused entry yields its original descriptor by its owned
    index, not by a new injectivity axiom for opaque platform assertions. *)
Lemma mutex_del_wrapper_takes_retained_descriptor : forall external platform port
  (abi : Armv7aContinuationABI external platform port) deposited focus sg state incoming fragments node
  (frame : Assertion) heap,
  let retained := mutex_del_retained_continuation_abi external platform port abi deposited in
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (armv7a_continuation_world retained focus (kernel_program_inv sg) state ** frame) heap ->
  armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) /\
  armv7a_continuation_binding deposited /\ armv7a_continuation_focus_binding focus deposited /\
  deposited.(armv7a_continuation_stack) = incoming /\
  deposited.(armv7a_continuation_fragments) = fragments /\
  (armv7a_continuation_world retained focus (kernel_program_inv sg)
     (os_int_exit_wrapper_restored_state state incoming) **
   task_stack_fragments_rep deposited.(armv7a_continuation_stack).(stackLeaseRegion)
     deposited.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation abi deposited ** frame) heap.
Proof.
  intros external platform port abi deposited focus sg state incoming fragments node frame heap retained
    Hcurrent Hnode Hparked Hfocus Haddress Hpre.
  assert (Hsplit : armv7a_continuation_world retained focus (kernel_program_inv sg) state ** frame |--
    armv7a_continuation_world retained focus (UCOS2_inv sg) state ** (unmap_table_rep sg ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  destruct (armv7a_wrapper_take_continuation external platform port retained focus sg state incoming fragments node
    _ heap Hcurrent Hnode Hparked Hfocus Haddress (Hsplit heap Hpre))
    as [Hreads [saved [Hbinding [Hfocused [Hstack [Hfragments Howned]]]]]].
  assert (Hrecover : armv7a_continuation_world retained focus (UCOS2_inv sg)
      (os_int_exit_wrapper_restored_state state incoming) **
    task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
    armv7a_dormant_continuation retained saved ** (unmap_table_rep sg ** frame) |--
    coq_prop (saved = deposited) &&
    (armv7a_continuation_world retained focus (kernel_program_inv sg)
       (os_int_exit_wrapper_restored_state state incoming) **
     task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
     armv7a_dormant_continuation abi saved ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap.
    change (armv7a_continuation_world retained focus (UCOS2_inv sg)
        (os_int_exit_wrapper_restored_state state incoming) **
      task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
      (coq_prop (saved = deposited) && armv7a_dormant_continuation abi saved) **
      (unmap_table_rep sg ** frame) |--
      coq_prop (saved = deposited) &&
      ((armv7a_continuation_world retained focus (UCOS2_inv sg)
          (os_int_exit_wrapper_restored_state state incoming) ** unmap_table_rep sg) **
       task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
       armv7a_dormant_continuation abi saved ** frame)).
    entailer!. }
  destruct (Hrecover heap Howned) as [Hsame Hpost].
  change (saved = deposited) in Hsame; subst saved.
  split; [exact Hreads|]. split; [exact Hbinding|]. split; [exact Hfocused|].
  split; [exact Hstack|]. split; [exact Hfragments|]. rewrite Hstack, Hfragments; exact Hpost.
Qed.

(** A SUPPLIED actual return, with the descriptor recovered from owned
    metadata. The physical source joins below are discharged by the entry
    store/save observations in the end-to-end consumer, not by an ABI law. *)
Lemma mutex_del_retained_wrapper_return : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  deposited sg handler original state node bx_pc written cursor before restored final_cursor after (frame : Assertion),
  let retained := mutex_del_retained_continuation_abi external platform port abi deposited in
  let focus := armv7a_call_focus original bx_pc deposited.(armv7a_continuation_lr) in
  state.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), deposited.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(tcbStkPtr) = deposited.(armv7a_continuation_sp) ->
  cursor.(kernel_restore_lr) = deposited.(armv7a_continuation_lr) ->
  cursor.(kernel_restore_msr_word) = Some written ->
  armv7a_irq_fiq_mask deposited.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask written ->
  (armv7a_continuation_world retained focus (kernel_program_inv sg) state **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)) before ->
  armv7a_continuation_restore_reads deposited before ->
  armv7a_restore_transition abi handler deposited before restored ->
  armv7a_restore_suffix_transition restore cursor restored final_cursor after ->
  armv7a_irq_restore_pointer_reads sg before
    (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) deposited.(armv7a_continuation_sp) /\
  final_cursor.(kernel_restore_return_word) = Some deposited.(armv7a_continuation_lr) /\
  (kernel_program_closed platform critical sg original.(os_sched_call_invocation)
     original.(os_sched_call_origin) (armv7a_irq_fiq_mask written)
     (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) **
   os_sched_context_resources external (armv7a_continuation_resumed_call deposited original) **
   armv7a_parked_continuations retained focus
     (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) after.
Proof.
  intros external platform port critical arch abi restore deposited sg handler original state node bx_pc
    written cursor before restored final_cursor after frame retained focus Hcurrent Hnode Hparked Haddress
    Hsp Hlr Hword Hmask Hpre Hreads Hrestore Hsuffix.
  destruct (mutex_del_wrapper_takes_retained_descriptor external platform port abi deposited focus sg state
    original.(os_sched_call_stack) deposited.(armv7a_continuation_fragments) node _ before
    Hcurrent Hnode Hparked eq_refl Haddress Hpre)
    as [Hpointers [Hbinding [Hfocused [Hstack [Hfragments Howned]]]]].
  destruct Hfocused as [Hcall [Hpc Hsavedlr]].
  assert (Horder : armv7a_continuation_world retained focus (kernel_program_inv sg)
      (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) **
    task_stack_fragments_rep deposited.(armv7a_continuation_stack).(stackLeaseRegion)
      deposited.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi deposited **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep deposited.(armv7a_continuation_stack).(stackLeaseRegion)
      deposited.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi deposited **
    (armv7a_continuation_world retained focus (kernel_program_inv sg)
      (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) ** frame)) by entailer!.
  destruct (armv7a_restore_call_resources external platform port abi handler deposited original _ before restored
    Hcall Hreads (Horder before Howned) Hrestore) as [Hmemory Hresumed].
  rewrite Hmask in Hresumed.
  assert (Hassociate : kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call deposited original) (armv7a_irq_fiq_mask written) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (armv7a_continuation_world retained focus (kernel_program_inv sg)
       (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) ** frame) |--
    kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call deposited original) (armv7a_irq_fiq_mask written) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     (armv7a_continuation_world retained focus (kernel_program_inv sg)
        (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) ** frame))) by entailer!.
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore
    (armv7a_continuation_resumed_call deposited original) written cursor restored final_cursor after _
    Hword (Hassociate restored Hresumed) Hsuffix) as [Hfinal [Hfinal_mem Hpost]].
  split; [rewrite <- Hsp; exact Hpointers|]. split.
  - rewrite Hfinal; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - assert (Hclose : kernel_call_execution_owned external platform
        (armv7a_continuation_resumed_call deposited original) (armv7a_irq_fiq_mask written) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (armv7a_continuation_world retained focus (kernel_program_inv sg)
          (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) ** frame)) |--
      kernel_program_closed platform critical sg original.(os_sched_call_invocation)
        original.(os_sched_call_origin) (armv7a_irq_fiq_mask written)
        (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) **
      os_sched_context_resources external (armv7a_continuation_resumed_call deposited original) **
      armv7a_parked_continuations retained focus
        (os_int_exit_wrapper_restored_state state original.(os_sched_call_stack)) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame).
    { unfold kernel_call_execution_owned, armv7a_continuation_world.
      rewrite kernel_program_closed_equiv.
      cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
    exact (Hclose after Hpost).
Qed.

(** The actual supplied ordinary normal return. In contrast to the earlier
    existential continuation cut, there is no post-take SP or CPSR-mask
    premise: both follow from this save's observations/entry store and its
    retained resource index. The linked source entry/BX address is still an
    explicit code-layout input, not a guessed return guarantee. The finite
    registry, physical caller/handler input and nonswitching scope remain. *)
Lemma mutex_del_restore_retained_ordinary_return : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg handler cpu_word entry checkpoint node deposited publication restore_entry_address cursor
  before written_cursor released saved_heap handler_heap Local local_step normal_return
  (bsp : RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    local_step normal_return)
  handler_cursor returned_cursor returned_heap exit_cursor exit_heap exit_kind exited_heap
  restored final_cursor after (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc) deposited.(armv7a_continuation_lr) in
  let retained := mutex_del_retained_continuation_abi external platform port abi deposited in
  let parked := armv7a_irq_live_parked_state checkpoint call deposited.(armv7a_continuation_sp)
    deposited.(armv7a_continuation_fragments) in
  handler.(os_int_exit_interrupted_pc) = restore_entry_address + 8 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask cpu_word ->
  checkpoint.(SchedState).(isRunning) = true -> checkpoint.(IntrState).(intNesting) = 0 ->
  checkpoint.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  checkpoint.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  checkpoint.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    deposited.(armv7a_continuation_fragments) ->
  task_publication_happened checkpoint.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) deposited.(armv7a_continuation_sp) ->
  deposited.(armv7a_continuation_lr) = cursor.(kernel_restore_lr) ->
  cursor.(kernel_restore_r0) = cpu_word ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (exit_kind = MutexDelRestoreSamePriority -> checkpoint.(SchedState).(readyList) <> []) ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) cpu_word entry ** os_sched_context_resources external call **
   (kernel_program_inv sg checkpoint **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  armv7a_save_transition abi handler deposited released saved_heap ->
  kernel_heap_execution
    (armv7a_irq_live_entry_writes sg checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
      deposited.(armv7a_continuation_sp)) saved_heap handler_heap ->
  normal_return sg handler_cursor handler_heap returned_cursor returned_heap ->
  local_step returned_cursor returned_heap exit_cursor exit_heap ->
  mutex_del_restore_exit_execution sg exit_kind exit_heap exited_heap ->
  armv7a_continuation_restore_reads deposited exited_heap ->
  armv7a_restore_transition abi handler deposited exited_heap restored ->
  armv7a_restore_suffix_transition restore written_cursor restored final_cursor after ->
  exists body_state,
    body_state.(TskState) = parked.(TskState) /\ body_state.(SchedState) = parked.(SchedState) /\
    restore_handler_execution local_step sg handler_cursor handler_heap returned_cursor returned_heap /\
    returned_cursor.(restore_handler_current_call) = handler_cursor.(restore_handler_current_call) /\
    returned_cursor.(restore_handler_pc) = handler_cursor.(restore_handler_current_call).(restore_handler_return_word) /\
    deposited.(armv7a_continuation_pc) = restore_entry_address + 8 /\
    armv7a_irq_restore_pointer_reads sg exited_heap
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) deposited.(armv7a_continuation_sp) /\
    final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
    (kernel_program_closed platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) (armv7a_irq_fiq_mask cpu_word)
       (os_int_exit_wrapper_restored_state (mutex_del_restore_exit_state exit_kind body_state) call.(os_sched_call_stack)) **
     os_sched_context_resources external (armv7a_continuation_resumed_call deposited call) **
     armv7a_parked_continuations retained focus
       (os_int_exit_wrapper_restored_state (mutex_del_restore_exit_state exit_kind body_state) call.(os_sched_call_stack)) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port critical arch abi restore sg handler cpu_word entry checkpoint node deposited publication
    restore_entry_address cursor before written_cursor released saved_heap handler_heap Local local_step normal_return bsp
    handler_cursor returned_cursor returned_heap exit_cursor exit_heap exit_kind exited_heap restored final_cursor after frame
    call focus retained parked Hbx Hhandler_mask Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hlr Hr0 Hmask Hready Hpre Hprefix Hsave Hentry Hreturn Hwrapper Hexit Hreads Hrestore Hsuffix.
  destruct (kernel_program_restore_prefix_irq_input external platform port critical arch abi restore
    sg handler cpu_word entry checkpoint cursor before written_cursor released frame
    Hhandler_mask Hnone Hr0 Hmask Hpre Hprefix) as [Hwritten [Hprefix_mem Hirq]].
  assert (Hdeposit_pre : (os_int_exit_frame_save_pre external platform handler **
    (armv7a_continuation_world abi focus (kernel_program_inv sg) checkpoint ** frame)) released).
  { unfold focus; rewrite Hlr; exact Hirq. }
  destruct (mutex_del_irq_source_deposits_retained_descriptor external platform port abi sg checkpoint node
    handler deposited publication frame released saved_heap Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hdeposit_pre Hsave)
    as [produced [Hcall [Hpc [Hsaved_mask [Hsave_writes [Hentry_run Hhandler]]]]]].
  assert (produced = handler_heap) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hhandler_pre : (armv7a_continuation_world retained focus (kernel_program_inv sg) parked **
    (mutex_del_restore_handler_owner platform port handler ** frame)) handler_heap).
  { assert (Horder : armv7a_continuation_world retained focus (kernel_program_inv sg) parked **
        (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
         os_int_exit_context_resources port handler ** frame) |--
      armv7a_continuation_world retained focus (kernel_program_inv sg) parked **
        (mutex_del_restore_handler_owner platform port handler ** frame)).
    { unfold mutex_del_restore_handler_owner; entailer!. }
    exact (Horder handler_heap Hhandler). }
  destruct (restore_handler_normal_return_preserves_world external platform port retained focus Local
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    local_step normal_return bsp sg parked handler_cursor handler_heap returned_cursor returned_heap frame Hreturn Hhandler_pre)
    as [body_state [Htrace [Hsame [Hreturn_pc [Ht [Hs Hbody]]]]]].
  assert (Hprivate_first : armv7a_continuation_world retained focus (kernel_program_inv sg) body_state **
      (mutex_del_restore_handler_owner platform port handler ** frame) |--
    mutex_del_restore_handler_owner platform port handler **
      (armv7a_continuation_world retained focus (kernel_program_inv sg) body_state ** frame)) by entailer!.
  pose proof (restore_handler_local_resources _ _ _ bsp returned_cursor returned_heap exit_cursor exit_heap _
    Hwrapper (Hprivate_first returned_heap Hbody)) as Hmasked_handler.
  assert (Hworld_first : mutex_del_restore_handler_owner platform port handler **
      (armv7a_continuation_world retained focus (kernel_program_inv sg) body_state ** frame) |--
    armv7a_continuation_world retained focus (kernel_program_inv sg) body_state **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)).
  { unfold mutex_del_restore_handler_owner; entailer!. }
  assert (Hbody_ready : exit_kind = MutexDelRestoreSamePriority -> body_state.(SchedState).(readyList) <> []).
  { intros Hkind; rewrite Hs; unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    rewrite Hrunning; exact (Hready Hkind). }
  pose proof (mutex_del_restore_exit_preserves_world external platform port retained focus sg exit_kind body_state _
    exit_heap exited_heap Hbody_ready (Hworld_first exit_heap Hmasked_handler) Hexit) as Hexit_world.
  set (exited := mutex_del_restore_exit_state exit_kind body_state) in *.
  destruct (mutex_del_restore_parked_wrapper_binding checkpoint call deposited.(armv7a_continuation_sp)
    deposited.(armv7a_continuation_fragments) node Hrunning Hcurrent Hnode) as [Hpark_current [Hpark_node Hparked]].
  assert (Hexit_current : exited.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold exited, mutex_del_restore_exit_state; destruct exit_kind;
      cbn [os_int_exit_selection_state os_int_exit_counter_state replace_IntrS replace_SchedS SchedState
        sched_refresh_high curTaskID]; rewrite Hs; exact Hpark_current. }
  assert (Hexit_node : exited.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node deposited.(armv7a_continuation_sp))).
  { unfold exited, mutex_del_restore_exit_state; destruct exit_kind;
      cbn [os_int_exit_selection_state os_int_exit_counter_state replace_IntrS replace_SchedS TskState];
      rewrite Ht; exact Hpark_node. }
  assert (Hexit_parked : exited.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), deposited.(armv7a_continuation_fragments))).
  { unfold exited, mutex_del_restore_exit_state; destruct exit_kind;
      cbn [os_int_exit_selection_state os_int_exit_counter_state replace_IntrS replace_SchedS TskState];
      rewrite Ht; exact Hparked. }
  set (written := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hwritten_mask : armv7a_irq_fiq_mask written = armv7a_irq_fiq_mask cpu_word).
  { unfold written; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity. }
  assert (Hsaved_written : armv7a_irq_fiq_mask deposited.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask written)
    by congruence.
  assert (Hcursor_lr : written_cursor.(kernel_restore_lr) = deposited.(armv7a_continuation_lr)).
  { rewrite Hwritten; cbn [kernel_restore_write_cpsr kernel_restore_lr]; symmetry; exact Hlr. }
  assert (Hword : written_cursor.(kernel_restore_msr_word) = Some written) by (rewrite Hwritten; reflexivity).
  destruct (mutex_del_retained_wrapper_return external platform port critical arch abi restore deposited sg handler
    call exited (task_set_saved_sp node deposited.(armv7a_continuation_sp)) handler.(os_int_exit_interrupted_pc)
    written written_cursor exited_heap restored final_cursor after frame Hexit_current Hexit_node Hexit_parked Haddress
    eq_refl Hcursor_lr Hword Hsaved_written Hexit_world Hreads Hrestore Hsuffix) as [Hpointers [Hfinal Hpost]].
  exists body_state; split; [exact Ht|]. split; [exact Hs|]. split; [exact Htrace|].
  split; [exact Hsame|]. split; [exact Hreturn_pc|]. split; [congruence|].
  split; [exact Hpointers|]. split; [rewrite Hlr in Hfinal; exact Hfinal|].
  rewrite Hwritten_mask in Hpost; exact Hpost.
Qed.
