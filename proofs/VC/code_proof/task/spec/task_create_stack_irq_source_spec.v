Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Producer at TCBInit's final real Restore: consume the saved/inside
    handles at MSR, then the actual IRQ save and the kernel's nesting/SP
    stores. This deposits the current whole map and the pending call into
    the existing client registry. Nothing is reconstructed from the old
    weak Restore postcondition. The selected caller is live at this source
    cut; the free-current self-delete path is not asserted to be this case. *)
Lemma task_create_restore_irq_deposit : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry released node handler suspended publication saved cursor before
  written_cursor irq_input saved_heap (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
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
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg released **
   task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  exists registry_heap,
    written_cursor = kernel_restore_write_cpsr cursor /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
      saved_heap registry_heap /\
    armv7a_continuation_binding suspended /\ suspended.(armv7a_continuation_call) = Some call /\
    armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask saved /\
    UCOS2_state_inv sg parked /\
    task_saved_pointer_at parked suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) /\
    (kernel_client_call_stack_world abi sg focus
       (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))
       parked **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) registry_heap.
Proof.
  intros environment critical arch restore sg entry released node handler suspended publication saved
    cursor before written_cursor irq_input saved_heap frame call abi Hslice Hrunning Hnesting Hcurrent
    Hnode Hid Hgeneration Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask
    Hhandler_mask Hpre Hprefix Hsave parked focus.
  match type of Hpre with ?P before => assert (Hrelease_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame))
  end.
  { unfold task_tcb_init_stack_context; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region _ _ _ _ restore sg call saved entry
    cursor before written_cursor irq_input _ Hr0 Hmask (Hrelease_input before Hpre) Hprefix)
    as [Hcursor [Hmemory Hreleased]].
  match type of Hreleased with ?P irq_input => assert (Hirq_input : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      handler **
    (UCOS2_inv sg released ** armv7a_task_stack_continuations abi released.(TskState)
      released.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame)))
  end.
  { unfold os_int_exit_frame_save_pre, task_tcb_init_stack_covered_capsules.
    rewrite Hhandler_mask; entailer!. }
  destruct (armv7a_irq_source_save_parks_call _ _ _ abi sg released node handler suspended publication
    (unmap_table_rep sg ** frame) irq_input saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid
    Hgeneration Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    (Hirq_input irq_input Hreleased) Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered Hparked]]]].
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hsaved_mask [Hpc [Hsaved_sp Hsaved_fragments]]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask released.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments released.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hpointer : task_saved_pointer_at parked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { unfold task_saved_pointer_at; rewrite Hlease, Htasks.
    exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)); split.
    - cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates];
        rewrite Z.eqb_refl; reflexivity.
    - change (node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
        suspended.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp)); auto. }
  assert (Hlookup : parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite Htasks, Hlease; apply task_stack_park_fragments_lookup. }
  assert (Hvalid : UCOS2_state_inv sg parked).
  { match type of Hparked with ?P registry_heap => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg parked) && TT)
    end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hparked)). }
  exists registry_heap; split; [exact Hcursor|]. split; [exact Hwrites|]. split; [exact Hstores|].
  split; [exact Hbinding|]. split; [exact Hcall|].
  split; [rewrite Hhandler_mask in Hsaved_mask; exact Hsaved_mask|].
  split; [exact Hvalid|]. split; [exact Hpointer|].
  match type of Hparked with ?P registry_heap => assert (Hclose : P |--
    kernel_client_call_stack_world abi sg focus
      (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))
      parked **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame))
  end.
  { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts, focus.
    rewrite kernel_program_inv_split_unmap, Hpc; entailer!. }
  exact (Hclose registry_heap Hparked).
Qed.

(** Publication changes the old head's links, so whole-node equality is
    not used. Its real field transformer preserves the running caller's
    generation, ID and absence from the parked map. The new child occupies
    a private slot and hence cannot be this already live caller. *)
Lemma task_create_publication_keeps_running_storage : forall sg publication state call node history,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_publication_happened state.(TskState) history
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  let published := task_create_stack_publication_state sg publication state in
  published.(SchedState).(isRunning) = state.(SchedState).(isRunning) /\
  published.(IntrState).(intNesting) = state.(IntrState).(intNesting) /\
  published.(SchedState).(curTaskID) = state.(SchedState).(curTaskID) /\
  task_publication_happened published.(TskState) history
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) /\
  published.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  exists current,
    published.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    current.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) /\
    current.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros sg publication state call node history Hvalid Hinput Hnode Hid Hgen Hnone Hhistory published.
  set (args := task_create_stack_publication_args publication).
  set (new := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) new).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) new.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) new.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) (task_commit_identity_private _ _ _ _ Hidentity))). }
  assert (Hdifferent : call.(os_sched_call_stack).(stackLeaseSlot) <> new.(taskID)) by congruence.
  destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _
    (proj1 (proj2 (proj2 (proj2 Hinput)))) Hidentity) as [Hnewslot Hnewgen].
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) new call.(os_sched_call_stack).(stackLeaseSlot)
    node Hfresh Hnode) as [current [Hcurrent Hfields]].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - unfold task_publication_happened in *.
    change (In (history, call.(os_sched_call_stack).(stackLeaseSlot),
      call.(os_sched_call_stack).(stackLeaseGeneration))
      ((publication.(stack_publication_invocation), new.(taskID), new.(taskGeneration)) ::
       state.(TskState).(taskLifecycle).(taskPublications))).
    right; exact Hhistory.
  - split.
    + change ((task_stack_park state.(TskState).(parkedTaskStacks)
        publication.(stack_publication_lease) (task_create_stack_publication_words publication))
        (task_stack_key call.(os_sched_call_stack)) = None).
      rewrite task_stack_park_lookup_other; [exact Hnone|].
      intro Heq; apply Hdifferent; rewrite Hnewslot; exact (f_equal fst Heq).
    + exists current; split; [exact Hcurrent|].
      pose proof (f_equal taskID Hfields) as Hcurrent_id.
      pose proof (f_equal taskGeneration Hfields) as Hcurrent_gen.
      change (current.(taskID) = node.(taskID)) in Hcurrent_id.
      change (current.(taskGeneration) = node.(taskGeneration)) in Hcurrent_gen.
      rewrite Hcurrent_id, Hcurrent_gen; auto.
Qed.

(** Actual TCBInit publication stores now feed the MSR/IRQ producer above.
    The input is the real tail-storage cut produced by the existing
    initialization/link-store proof, including the child's StackInit bytes.
    The execution owner, saved token and inactive handler stack are framed
    only through these local C writes; the whole OS world then moves into
    the handler at the actual IRQ boundary. *)
Lemma task_create_publication_restore_irq_deposit : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry current node handler publication history saved (frame : Assertion) before,
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  0 <= (task_create_stack_publication_args publication).(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  current.(SchedState).(isRunning) = true -> current.(IntrState).(intNesting) = 0 ->
  current.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  current.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  current.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  task_publication_happened current.(TskState) history
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_live_coverage current.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
     current publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) **
   (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
    unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) before ->
  let published := task_create_stack_publication_state sg publication current in
  exists publication_heap,
    task_tcb_init_publication_tail_fragment sg
      (task_create_stack_publication_args publication).(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before publication_heap /\
    kernel_client_step (task_create_stack_publication_client publication) sg current published /\
    (forall suspended cursor written_cursor irq_input saved_heap,
      armv7a_task_frame_slice suspended ->
      valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
      task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
        suspended.(armv7a_continuation_fragments) ->
      task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_sp) ->
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor publication_heap written_cursor irq_input ->
      armv7a_save_transition abi handler suspended irq_input saved_heap ->
      let parked := armv7a_irq_live_parked_state published call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments) in
      let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
      exists registry_heap,
        written_cursor = kernel_restore_write_cpsr cursor /\
        kernel_heap_writes (armv7a_continuation_save_writes suspended)
          irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
        kernel_heap_execution (armv7a_irq_live_entry_writes sg published
          call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
        armv7a_continuation_binding suspended /\ suspended.(armv7a_continuation_call) = Some call /\
        armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask saved /\
        UCOS2_state_inv sg parked /\
        task_saved_pointer_at parked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
        (kernel_client_call_stack_world abi sg focus
           (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))
           parked **
         (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
            handler.(os_int_exit_origin) 192 **
          os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) registry_heap).
Proof.
  intros environment critical arch restore sg entry current node handler publication history saved frame before
    call abi Hvalid Hinput Hpriority Hpointer Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hhistory Hcoverage Hhandler_mask Hpre published.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
      current publication.(stack_publication_slot) publication.(stack_publication_image) **
    (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
     armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) **
     (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
      unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame))) by entailer!
  end.
  destruct (task_tcb_init_publication_tail_store_execution sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) current publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid (proj1 (proj2 (proj2 Hinput)))
    Hpriority Hpointer (Horder before Hpre)) as [publication_heap [Hstores Hstored]].
  pose proof (task_create_publication_covered_stack_merge _ _ _ abi sg publication current
    (Some (task_stack_key call.(os_sched_call_stack))) Hvalid Hinput Hcoverage) as Hmerge;
    cbv zeta in Hmerge.
  match type of Hstored with ?P publication_heap => assert (Hclosed : P |--
    coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current published /\
      task_stack_live_coverage published.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
     UCOS2_inv sg published ** task_tcb_init_stack_covered_capsules environment published **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame))
  end.
  { unfold task_tcb_init_stack_covered_capsules; sepcon_assoc_change;
      sep_apply_l_atomic Hmerge; Intros; entailer!. }
  destruct (Hclosed publication_heap Hstored) as [[Hstep Hcovered] Hworld].
  destruct (task_create_publication_keeps_running_storage sg publication current call node history
    Hvalid Hinput Hnode Hid Hgen Hnone Hhistory)
    as [Hr [Hn [Hc [Hhistory_after [Habsent [updated [Hupdated [Hupdated_id Hupdated_gen]]]]]]]].
  exists publication_heap; split; [exact Hstores|]. split; [exact Hstep|].
  intros suspended cursor written_cursor irq_input saved_heap Hslice Hregion Hgeometry Hsp Hr0 Hmask Hprefix Hsave.
  eapply task_create_restore_irq_deposit with (node := updated) (publication := history); try eassumption.
Qed.
