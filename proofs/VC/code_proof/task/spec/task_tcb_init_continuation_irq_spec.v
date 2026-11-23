Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This IRQ happens after the C Restore's MSR. Its own Save/inside pair
    has already been consumed. The local view retains the actual saved
    descriptor, not another CPU token, stack byte, or Scheduler mask=192
    assumption. Other keys keep all their original local resources. *)
Definition task_tcb_init_irq_local (saved_local : Armv7aContinuation -> Assertion)
  (suspended descriptor : Armv7aContinuation) : Assertion :=
  if task_stack_key_eq_dec (task_stack_key descriptor.(armv7a_continuation_stack))
      (task_stack_key suspended.(armv7a_continuation_stack))
  then coq_prop (descriptor = suspended) && emp
  else task_create_continuation_local saved_local descriptor.

Lemma task_tcb_init_irq_local_saved_eq : forall saved_local suspended,
  task_tcb_init_irq_local saved_local suspended suspended =
    (coq_prop (suspended = suspended) && emp).
Proof.
  intros; unfold task_tcb_init_irq_local.
  destruct task_stack_key_eq_dec; [reflexivity|contradiction].
Qed.

(** An absent entry owns nothing, so focusing/unfocusing that key changes
    no existing entry. This never forgets the local of a present key. *)
Lemma task_tcb_init_irq_map_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks saved_local suspended,
  stacks (task_stack_key suspended.(armv7a_continuation_stack)) = None ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (task_create_continuation_local saved_local)) stacks --||--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (task_tcb_init_irq_local saved_local suspended)) stacks.
Proof.
  intros external platform port abi tasks stacks saved_local suspended Hnone.
  split; (unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono;
    intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor;
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto;
    assert (Hdifferent : task_stack_key descriptor.(armv7a_continuation_stack) <>
      task_stack_key suspended.(armv7a_continuation_stack))
      by (intro Heq; rewrite <- Hkey, Heq, Hnone in Hlookup; discriminate);
    Exists descriptor; unfold task_tcb_init_irq_local;
    destruct task_stack_key_eq_dec; [contradiction|entailer!]).
Qed.

(** A real publication has a fresh key. With the interrupted key already
    parked, its initialized None entry uses exactly emp, even under this
    precise IRQ view. This is an OS allocation consequence, not a law
    about an arbitrary [saved_local]. *)
Lemma task_tcb_init_irq_publication_local : forall sg publication state saved_local suspended payload,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) = Some payload ->
  task_tcb_init_irq_local saved_local suspended (task_create_stack_publication_continuation publication) = emp.
Proof.
  intros sg publication state saved_local suspended payload Hvalid Hinput Hparked.
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hcommit.
  pose proof (proj1 (proj2 (proj2 (proj2 Hinput)))) as Hcreation.
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node)
    by (eapply task_tcb_init_commit_binding_identity; exact Hcommit).
  destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _ Hcreation Hidentity) as [Hslot Hgen].
  assert (Hconsistent : parked_stacks_consistent state.(TskState) state.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hfresh : state.(TskState).(parkedTaskStacks)
    (task_stack_key publication.(stack_publication_lease)) = None).
  { unfold task_stack_key; rewrite <- Hslot, <- Hgen.
    eapply task_commit_stack_key_absent; [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hconsistent]. }
  unfold task_tcb_init_irq_local.
  change ((if task_stack_key_eq_dec (task_stack_key publication.(stack_publication_lease))
      (task_stack_key suspended.(armv7a_continuation_stack))
    then coq_prop (task_create_stack_publication_continuation publication = suspended) && emp else emp) = emp).
  destruct task_stack_key_eq_dec as [Heq|Hne]; [rewrite Heq, Hparked in Hfresh; discriminate|reflexivity].
Qed.

Lemma task_tcb_init_irq_publication_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication state saved_local suspended payload
  (frame : Assertion) before after,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  task_stack_live_coverage state.(TskState) None ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) = Some payload ->
  0 <= (task_create_stack_publication_args publication).(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
     state publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
     state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame) before ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  kernel_client_step (task_create_stack_publication_client publication) sg state
    (task_create_stack_publication_state sg publication state) /\
  (kernel_client_continuation_world abi (task_tcb_init_irq_local saved_local suspended) sg
    (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros external platform port abi sg publication state saved_local suspended payload frame before after
    Hvalid Hinput Hcoverage Hparked Hpriority Hpointer Hpre Hsource.
  pose proof (task_tcb_init_irq_publication_local sg publication state saved_local suspended payload
    Hvalid Hinput Hparked) as Hlocal.
  match type of Hpre with ?P before => assert (Hpack : P |--
    kernel_client_continuation_publication abi (task_tcb_init_irq_local saved_local suspended)
      sg publication state ** frame) end.
  { unfold kernel_client_continuation_publication; rewrite Hlocal; entailer!. }
  eapply kernel_client_publication_continuation_resources; [exact (Hpack before Hpre)|exact Hsource].
Qed.

(** The real two pointer reads and take recover the very descriptor
    deposited by this IRQ. The remaining generic map is preserved, and
    only the now-absent precise IRQ key is returned to the base family. *)
Lemma task_tcb_init_irq_take_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state saved_local suspended call node
  (frame : Assertion) heap,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
     state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot))
    suspended.(armv7a_continuation_sp) /\
  armv7a_continuation_restore_reads suspended heap /\
  task_stack_live_coverage restored.(TskState) (Some (task_stack_key suspended.(armv7a_continuation_stack))) /\
  (UCOS2_inv sg restored ** store_parked_continuations
     (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
     restored.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended ** frame) heap.
Proof.
  intros external platform port abi sg state saved_local suspended call node frame heap
    Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre restored.
  assert (Hpointers : armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) node.(tcbStkPtr)).
  { match type of Hpre with ?P heap => assert (Horder : P |-- UCOS2_inv sg state **
      (store_parked_continuations
        (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
        state.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
    destruct (Horder heap Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_live; eassumption. }
  match type of Hpre with ?P heap => assert (Htake : P |--
    coq_prop (armv7a_continuation_binding suspended /\ armv7a_task_frame_slice suspended /\
      task_stack_live_sp state.(TskState) (task_stack_key suspended.(armv7a_continuation_stack))
        suspended.(armv7a_continuation_sp)) &&
    (UCOS2_inv sg restored ** store_parked_continuations
       (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
       restored.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
       suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended ** frame)) end.
  { rewrite UCOS2_inv_split_parked_stacks; Intros.
    assert (Hvalid : UCOS2_state_inv sg state) by assumption.
    assert (Hconsistent : parked_stacks_consistent state.(TskState)
      (task_stack_take state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_stack))).
    { apply task_stack_take_preserves_consistency.
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
    sep_apply_l_atomic (store_parked_stacks_take_fragments state.(TskState).(parkedTaskStacks)
      suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_fragments) Hparked).
    sep_apply_l_atomic (store_parked_continuations_take
      (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
      state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_fragments) Hparked).
    sep_apply_l_atomic (proj2 (task_tcb_init_irq_map_absent external platform port abi state.(TskState)
      (task_stack_take state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_stack))
      saved_local suspended (task_stack_take_lookup _ _))).
    unfold kernel_saved_continuation_entry at 2; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) =
      task_stack_key suspended.(armv7a_continuation_stack)) by tauto.
    unfold task_tcb_init_irq_local; rewrite Hkey.
    destruct task_stack_key_eq_dec as [Heq|Hne]; [|contradiction].
    Intros; assert (descriptor = suspended) by assumption; subst descriptor.
    sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg state _ Hvalid Hconsistent).
    unfold armv7a_task_continuation_resource; rewrite Hcall.
    unfold restored, os_int_exit_wrapper_restored_state;
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks]; entailer!. }
  destruct (Htake heap Hpre) as [[Hbinding [Hslice Hlive]] Hresources].
  assert (Hsp : node.(tcbStkPtr) = suspended.(armv7a_continuation_sp)) by (apply Hlive; assumption).
  rewrite Hsp in Hpointers; split; [exact Hpointers|]. split.
  - eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hresources with ?P heap => assert (Horder : P |--
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) **
      (UCOS2_inv sg restored ** store_parked_continuations
         (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
         restored.(TskState).(parkedTaskStacks) ** armv7a_dormant_continuation abi suspended ** frame))
      by entailer! end.
    exact (Horder heap Hresources).
  - split; [apply task_stack_take_covers_selected; exact Hcoverage|exact Hresources].
Qed.


(** A complete actual same-task IRQ suffix for the public annotation's
    Restore output. The physical edges are kept separate:
      C MSR -> IRQ save/nesting/SP/park -> actual built-in registry trace
      -> pointer loads/take -> IRQ restore -> the interrupted C BX.
    The registry subfamily starts Closed, hence contains counter steps;
    publication is separately checked above at its actual prepared cut.
    Extra/switching clients need their own source proofs and are not
    silently assigned a local-preservation contract here.

    We produce [restore_output], which the canonical caller consumes.
    [restore_post] asks for one flat registry trace from released to final;
    deposit and take are physical source edges rather than such registry
    steps. Their established observations compose without inventing that
    stronger flat trace, assuming eventual return, or adding an ABI law. *)
Lemma task_tcb_init_continuation_restore_irq_output :
  forall environment critical saved_local arch Extra
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg entry released node handler suspended publication saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let local := task_tcb_init_irq_local saved_local suspended in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
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
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  (task_tcb_init_continuation_restore_input environment critical saved_local sg call saved entry released **
   unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) before ->
  forall written irq_input saved_heap,
  armv7a_restore_prefix_transition restore cursor before written irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  exists registry_heap,
    written = kernel_restore_write_cpsr cursor /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
        KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned,
        @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
          KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin)
          parked false call.(os_sched_call_origin) returned /\
        armv7a_irq_restore_pointer_reads sg closed_heap
          (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp) /\
        (forall irq_return resume_cursor final_cursor after,
          armv7a_restore_transition abi handler suspended closed_heap irq_return ->
          resume_cursor.(kernel_restore_msr_word) = Some
            (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) ->
          resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
          armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
          final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
          (task_tcb_init_continuation_restore_output environment critical saved_local sg call saved released **
           unmap_table_rep sg **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           frame) after /\
          task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call /\
          task_tcb_init_stack_return_preserved call released
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) /\
          (task_tcb_init_continuation_save_input environment critical saved_local sg
             (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask saved)
             (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
           unmap_table_rep sg **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           frame) after)).
Proof.
  intros environment critical saved_local arch Extra restore sg entry released node handler suspended
    publication saved cursor before frame call abi local parked Horigin Hslice Hrunning Hnesting Hcurrent
    Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hr0 Hmask Hhandler
    Henter Hexit Hpublish Hpre written irq_input saved_heap Hprefix Hsave.
  assert (Hreleased_valid : UCOS2_state_inv sg released).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg released) && TT) end.
    { unfold task_tcb_init_continuation_restore_input, UCOS2_inv;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  assert (Hcoverage : task_stack_live_coverage released.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hpre with ?P before => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage released.(TskState) (task_stack_call_active_key call)) && TT) end.
    { unfold task_tcb_init_continuation_restore_input; entailer!; intros ? ?; exact I. }
    pose proof (proj1 (Hobserve before Hpre)) as Hcovered.
    unfold task_stack_call_active_key in Hcovered; rewrite Horigin in Hcovered; exact Hcovered. }
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hsave_source [Hcall [Hbinding [Hsaved_mask [Hpc [Hsaved_sp Hsaved_fragments]]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hbound; rewrite Hcall in Hbound; symmetry; exact Hbound. }
  assert (Habsent : released.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  match type of Hpre with ?P before => assert (Hrelease_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (UCOS2_inv sg released ** task_tcb_init_continuation_capsules environment saved_local released **
     unmap_table_rep sg **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold task_tcb_init_continuation_restore_input; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region _ _ _ _ restore sg call saved entry cursor before
    written irq_input _ Hr0 Hmask (Hrelease_input before Hpre) Hprefix) as [Hwritten [Hmemory Hreleased]].
  match type of Hreleased with ?P irq_input => assert (Hirq_input : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg released **
     store_parked_continuations (kernel_saved_continuation_entry abi released.(TskState) local)
       released.(TskState).(parkedTaskStacks) ** local suspended ** (unmap_table_rep sg ** frame))) end.
  { unfold task_tcb_init_continuation_capsules; fold abi.
    sep_apply_l_atomic (proj1 (task_tcb_init_irq_map_absent _ _ _ abi released.(TskState)
      released.(TskState).(parkedTaskStacks) saved_local suspended Habsent)).
    unfold os_int_exit_frame_save_pre, local.
    rewrite task_tcb_init_irq_local_saved_eq.
    rewrite Hhandler; entailer!. }
  destruct (kernel_irq_save_continuation_resources _ _ _ abi sg released node handler suspended publication
    local (unmap_table_rep sg ** frame) irq_input saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen
    Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Hirq_input irq_input Hreleased) Hsave)
    as [registry_heap [Hsave_call [Hsave_pc [Hsave_mask [Hwrites [Hstores [Hcovered Hparked]]]]]]].
  fold parked in Hcovered, Hparked.
  assert (Hparked_valid : UCOS2_state_inv sg parked).
  { match type of Hparked with ?P registry_heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hparked)). }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask released.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments released.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hparked_sched : parked.(SchedState) = released.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  match type of Hparked with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_continuation_world abi local sg parked **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
     frame)) end.
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_continuation_trace_resources _ _ _ Extra abi local critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None Henter Hexit Hpublish
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace parked
    call.(os_sched_call_origin) I (Hregistry registry_heap Hparked))
    as [returned [Hstates [Hsources [Hobserver Hworld]]]].
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg _ _ _ _ Hstates eq_refl)
    as [Hclosed [Hreturned_tasks Hreturned_sched]].
  assert (Hreturned_current : returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite Hreturned_sched, Hparked_sched; exact Hcurrent. }
  assert (Hreturned_node : returned.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { rewrite Hreturned_tasks, Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hreturned_lookup : returned.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite Hreturned_tasks, Htasks, Hlease.
    apply task_stack_park_fragments_lookup. }
  match type of Hworld with ?P closed_heap => assert (Htake_input : P |--
    coq_prop (task_stack_live_coverage returned.(TskState) None) &&
    (UCOS2_inv sg returned **
     store_parked_continuations (kernel_saved_continuation_entry abi returned.(TskState)
       (task_tcb_init_irq_local saved_local suspended)) returned.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      unmap_table_rep sg ** frame))) end.
  { unfold kernel_client_continuation_resources, kernel_client_continuation_world, local;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Htake_input closed_heap Hworld) as [Hreturned_coverage Htake_owned].
  assert (Htake_current : returned.(SchedState).(curTaskID) =
    Some suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Hreturned_current).
  assert (Htake_node : returned.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))) by (rewrite Hlease; exact Hreturned_node).
  assert (Htake_gen : (task_set_saved_sp node suspended.(armv7a_continuation_sp)).(taskGeneration) =
    suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) by (rewrite Hlease; exact Hgen).
  assert (Htake_address : tcb_field_address
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Haddress).
  destruct (task_tcb_init_irq_take_resources _ _ _ abi sg returned saved_local suspended call
    (task_set_saved_sp node suspended.(armv7a_continuation_sp)) _ closed_heap Hcall Htake_current Htake_node
    Htake_gen Hreturned_lookup Htake_address Hreturned_coverage Htake_owned)
    as [Hpointers [Hreads [Hfinal_coverage Htake_resources]]].
  exists returned; split; [exact Hstates|]. split; [exact Hsources|]. split.
  - rewrite Hlease in Hpointers; exact Hpointers.
  - intros irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix.
    match type of Htake_resources with ?P closed_heap => assert (Hrestore_input : P |--
      interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       unmap_table_rep sg ** frame)) end.
    { unfold task_tcb_init_continuation_capsules; entailer!. }
    destruct (armv7a_restore_call_resources _ _ _ abi handler suspended call _ closed_heap irq_return
      Hcall Hreads (Hrestore_input closed_heap Htake_resources) Hrestore) as [Hirq_memory Hirq_owned].
    assert (Hcomputed_mask : armv7a_irq_fiq_mask
      (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) =
      armv7a_irq_fiq_mask saved) by (rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity).
    rewrite Hsaved_mask, Hhandler in Hirq_owned.
    rewrite <- Hcomputed_mask in Hirq_owned.
    match type of Hirq_owned with ?P irq_return => assert (Hsuffix_input : P |--
      kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
        (armv7a_continuation_resumed_call suspended call)
        (armv7a_irq_fiq_mask
          (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))) **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       unmap_table_rep sg **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))
      by entailer! end.
    destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
      (armv7a_continuation_resumed_call suspended call) _ resume_cursor irq_return final_cursor after _
      Hword (Hsuffix_input irq_return Hirq_owned) Hsuffix) as [Hcursor [Hafter_memory Hafter]].
    rewrite Hcomputed_mask, Hlease in Hafter.
    assert (Hcurrent_valid : UCOS2_state_inv sg
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { match type of Hafter with ?P after => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))) && TT) end.
      { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve after Hafter)). }
    assert (Hpreserved : task_tcb_init_stack_return_preserved call released
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply task_tcb_init_stack_irq_return_preserved; eassumption. }
    assert (Hcall_preserved : task_tcb_init_call_preserved sg call.(os_sched_call_invocation) released
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply task_tcb_init_irq_preserves_call; eassumption. }
    assert (Hordinary : UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved call released
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { intro Hvalid; exact (proj2 (proj2 Hpreserved)). }
    split.
    + rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
    + assert (Hsame : task_tcb_init_stack_same_call
        (armv7a_continuation_resumed_call suspended call) call).
      { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
          cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack];
          repeat split; try reflexivity; exact Hlease. }
      match type of Hafter with ?P after => assert (Hsource_pack : P |--
        task_tcb_init_continuation_save_input environment critical saved_local sg
          (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask saved)
          (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
        unmap_table_rep sg **
        task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
        frame) end.
      { unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
          task_stack_call_active_key, armv7a_continuation_resumed_call, critical_region_outside.
        cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
        rewrite Hlease, Horigin, critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
        rewrite Hlease in Hfinal_coverage.
        unfold task_tcb_init_continuation_capsules, UCOS2_inv; entailer!. }
      pose proof (Hsource_pack after Hafter) as Hcurrent_owned.
      split.
      * match type of Hcurrent_owned with ?P after => match goal with |- ?Q after =>
          assert (Hlegacy : P |-- Q) end end.
        { unfold task_tcb_init_continuation_restore_output.
          Exists (armv7a_continuation_resumed_call suspended call)
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)); entailer!. }
        exact (Hlegacy after Hcurrent_owned).
      * split; [exact Hsame|]. split; [exact Hpreserved|exact Hcurrent_owned].
Qed.

(** The actual TCB final-Restore consumer.  The complete pre-existing
    publication/no-free result and its failed buffer are carried as the
    caller frame through the SAME existing IRQ producer.  Its exact take
    endpoint is consumed before it is hidden by the legacy Restore output.
    Only the already implemented Closed/counter return family is covered;
    arbitrary handlers and the initially-disabled Save boundary are not
    asserted here. No physical instruction proof or platform law is added. *)
Lemma task_tcb_init_continuation_restore_irq_sched_call_post :
  forall environment critical saved_local arch Extra
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg entry released node handler suspended publication saved cursor before
    region args task_return lower upper initial_name invocation origin mask initial original result (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let local := task_tcb_init_irq_local saved_local suspended in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  task_tcb_init_stack_same_call call original -> interrupt_saved_value mask saved ->
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial result released ->
  task_tcb_init_stack_source_preserved original initial released ->
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
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  (task_tcb_init_continuation_restore_input environment critical saved_local sg call saved entry released **
   unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)) before ->
  forall written irq_input saved_heap,
  armv7a_restore_prefix_transition restore cursor before written irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  exists registry_heap,
    written = kernel_restore_write_cpsr cursor /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
        KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned,
        @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
          KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin)
          parked false call.(os_sched_call_origin) returned /\
        armv7a_irq_restore_pointer_reads sg closed_heap
          (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp) /\
        (forall irq_return resume_cursor final_cursor after,
          armv7a_restore_transition abi handler suspended closed_heap irq_return ->
          resume_cursor.(kernel_restore_msr_word) = Some
            (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) ->
          resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
          armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
          final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
          (task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
             lower upper initial_name invocation origin mask initial original result **
           unmap_table_rep sg **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           frame) after)).
Proof.
  intros environment critical saved_local arch Extra restore sg entry released node handler suspended
    publication saved cursor before region args task_return lower upper initial_name invocation origin mask
    initial original result frame call abi local parked Hcaller Hsaved Hresult Hprefix
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hr0 Hmask Hhandler Henter Hexit Hpublish Hpre written irq_input saved_heap Hmsr Hsave.
  assert (Hvalid : UCOS2_state_inv sg released).
  { match type of Hpre with ?P before => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg released) && TT) end.
    { unfold task_tcb_init_continuation_restore_input, UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  destruct (task_tcb_init_continuation_restore_irq_output environment critical saved_local arch Extra restore
    sg entry released node handler suspended publication saved cursor before
    (task_tcb_init_stack_buffer_result region args task_return lower upper result ** frame)
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hr0 Hmask Hhandler Henter Hexit Hpublish Hpre
    written irq_input saved_heap Hmsr Hsave)
    as [registry_heap [Hwritten [Hwrites [Hstores Hfinish]]]].
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Hclients.
  destruct (Hfinish closed_heap Hclients)
    as [returned [Hstates [Hsource [Hpointers Hreturn]]]].
  exists returned; split; [exact Hstates|]. split; [exact Hsource|]. split; [exact Hpointers|].
  intros irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix.
  destruct (Hreturn irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix)
    as [Hreturned [Hlegacy [Hsame [Hpreserved Howned]]]].
  split; [exact Hreturned|].
  set (resumed := armv7a_continuation_resumed_call suspended call).
  fold resumed in Hsame, Howned.
  assert (Hresumed_same : task_tcb_init_stack_same_call resumed original).
  { unfold task_tcb_init_stack_same_call.
    split.
    - etransitivity; [exact (proj1 Hsame)|exact (proj1 Hcaller)].
    - split.
      + etransitivity; [exact (proj1 (proj2 Hsame))|exact (proj1 (proj2 Hcaller))].
      + etransitivity; [exact (proj2 (proj2 Hsame))|exact (proj2 (proj2 Hcaller))]. }
  assert (Horiginal_preserved : task_tcb_init_stack_return_preserved original released
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { destruct Hcaller as [Hinvocation [Hcall_origin Hstack]].
    unfold task_tcb_init_stack_return_preserved, task_tcb_init_stack_source_preserved,
      kernel_call_task_source in *.
    rewrite <- Hinvocation, <- Hcall_origin, <- Hstack; exact Hpreserved. }
  assert (Hresumed_stack : resumed.(os_sched_call_stack) = call.(os_sched_call_stack))
    by exact (proj2 (proj2 Hsame)).
  assert (Hparked : armv7a_irq_live_parked_state released resumed suspended.(armv7a_continuation_sp)
      suspended.(armv7a_continuation_fragments) = parked).
  { unfold parked, armv7a_irq_live_parked_state; rewrite Hresumed_stack; reflexivity. }
  assert (Hresumed_origin : resumed.(os_sched_call_origin) = RunningInvocation
      call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration)).
  { exact (eq_trans (proj1 (proj2 Hsame)) Horigin). }
  pose proof (task_tcb_init_continuation_builtin_take_sched_call_post environment critical saved_local Extra
    sg region args task_return lower upper initial_name invocation origin mask initial original result
    released resumed suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) returned)
    as Hclose.
  cbv zeta in Hclose; rewrite Hparked, Hresumed_stack in Hclose.
  specialize (Hclose Hresult Hvalid Hprefix Hresumed_same Hresumed_origin Hstates Horiginal_preserved).
  rewrite (proj2 Hsaved) in Howned.
  match type of Howned with ?P after => assert (Horder : P |--
    (task_tcb_init_continuation_save_input environment critical saved_local sg resumed mask
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     task_tcb_init_stack_buffer_result region args task_return lower upper result) **
    (unmap_table_rep sg **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     frame)) by entailer! end.
  pose proof (Horder after Howned) as Hordered.
  match type of Hordered with ?P after => match goal with |- ?Q after =>
    assert (Hcomplete : P |-- Q) end end.
  { sep_apply_l_atomic Hclose; entailer!. }
  exact (Hcomplete after Hordered).
Qed.


