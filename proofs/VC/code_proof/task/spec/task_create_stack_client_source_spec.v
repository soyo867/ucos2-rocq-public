Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A parked call's actual TCB SP, not a new ghost field. Keeping the
    generation and address through the client trace permits comparison of
    the sixteen original saved words with the eventual wrapper loads. *)
Definition task_saved_pointer_at (state : UCOS2_Verify_State)
  (lease : TaskStackLease) (sp : Z) : Prop :=
  exists node, state.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = lease.(stackLeaseGeneration) /\ node.(tcbStkPtr) = sp.

Lemma task_publication_preserves_saved_pointer : forall sg publication state lease sp,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  task_saved_pointer_at state lease sp ->
  task_saved_pointer_at (task_create_stack_publication_state sg publication state) lease sp.
Proof.
  intros sg publication state lease sp Hvalid Hinput [old [Hold [Hg Hsp]]].
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) node.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) (task_commit_identity_private _ _ _ _ Hidentity))). }
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node lease.(stackLeaseSlot) old Hfresh Hold)
    as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|].
  pose proof (f_equal taskGeneration Hfields) as Hgeneration.
  pose proof (f_equal tcbStkPtr Hfields) as Hpointer.
  change (current.(taskGeneration) = old.(taskGeneration)) in Hgeneration.
  change (current.(tcbStkPtr) = old.(tcbStkPtr)) in Hpointer.
  rewrite Hgeneration, Hpointer; auto.
Qed.

(** The same registered state trace as the spatial producer is used.
    Extra fragments supply their own OS-side field proof; this is not a
    new interpretation law of the CPU or a public Create precondition. *)
Lemma kernel_client_trace_preserves_saved_pointer : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg lease sp,
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> task_saved_pointer_at state lease sp ->
    UCOS2_state_inv sg returned /\ task_saved_pointer_at returned lease sp) ->
  forall cut state next returned,
  kernel_client_heap_state_trace extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> task_saved_pointer_at state lease sp ->
  UCOS2_state_inv sg returned /\ task_saved_pointer_at returned lease sp.
Proof.
  intros Extra extra_effect sg lease sp Hextra cut state next returned Htrace.
  induction Htrace; intros Hvalid Hpointer; [split; assumption|].
  apply IHHtrace.
  - destruct H.
    + apply os_int_enter_preserves_validity; exact Hvalid.
    + exact Hvalid.
    + eapply task_create_stack_publication_preserves_validity;
        [exact Hvalid|split; [exact H|reflexivity]].
    + exact (proj1 (Hextra _ _ _ _ H Hvalid Hpointer)).
  - destruct H.
    + exact Hpointer.
    + exact Hpointer.
    + eapply task_publication_preserves_saved_pointer; eassumption.
    + exact (proj2 (Hextra _ _ _ _ H Hvalid Hpointer)).
Qed.

(** Two descriptions of the SAME owned saved buffer, read at the SAME
    actual SP, agree on CPSR and all thirteen registers. Call/PC/LR focus
    alone would not justify these equalities. *)
Lemma armv7a_same_frame_registers : forall original selected (frame : Assertion) heap,
  armv7a_continuation_binding original -> armv7a_task_frame_slice original ->
  selected.(armv7a_continuation_stack) = original.(armv7a_continuation_stack) ->
  selected.(armv7a_continuation_fragments) = original.(armv7a_continuation_fragments) ->
  selected.(armv7a_continuation_sp) = original.(armv7a_continuation_sp) ->
  armv7a_continuation_restore_reads selected heap ->
  (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
    selected.(armv7a_continuation_fragments) ** frame) heap ->
  selected.(armv7a_continuation_cpsr) = original.(armv7a_continuation_cpsr) /\
  selected.(armv7a_continuation_registers) = original.(armv7a_continuation_registers).
Proof.
  intros original selected frame heap Hbinding Hslice Hlease Hfragments Hsp Hreads Hheap.
  assert (Horiginal : armv7a_continuation_restore_reads original heap).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    rewrite Hlease, Hfragments in Hheap; exact Hheap. }
  assert (Hwords : armv7a_continuation_words selected = armv7a_continuation_words original).
  { eapply armv7a_frame_word_reads_deterministic.
    - rewrite (armv7a_continuation_words_length selected (proj1 Hreads)),
        (armv7a_continuation_words_length original Hbinding); reflexivity.
    - pose proof (proj2 Hreads) as Hselected; rewrite Hsp in Hselected; exact Hselected.
    - exact (proj2 Horiginal). }
  unfold armv7a_continuation_words in Hwords; injection Hwords as Hcpsr Htail.
  split; [exact Hcpsr|].
  pose proof (f_equal (firstn 13) Htail) as Hregisters.
  rewrite !firstn_app, (proj1 (proj1 Hreads)), (proj1 Hbinding) in Hregisters.
  change (firstn 13 selected.(armv7a_continuation_registers) ++ [] =
    firstn 13 original.(armv7a_continuation_registers) ++ []) in Hregisters.
  rewrite !app_nil_r in Hregisters.
  rewrite !firstn_all2 in Hregisters by
    (pose proof (proj1 (proj1 Hreads)); pose proof (proj1 Hbinding); lia).
  exact Hregisters.
Qed.

(** Take the focused pending call at an actual wrapper-return cut. The
    descriptor and register equalities come from the same owned frame and
    TCB SP. Registry transport and selector/install are earlier producers;
    neither is assumed here as a desired public return. Both the registered
    wrapper consumer and the foreign-task switch consumer use this owner. *)
Lemma task_create_pending_call_stack_restore : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg original suspended,
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  forall returned after handler (frame : Assertion),
  task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  returned.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_client_call_stack_world abi sg focus payload returned **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) after ->
  let resumed := os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack) in
  exists selected,
    armv7a_irq_restore_pointer_reads sg after
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus selected /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    task_stack_live_coverage resumed.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) /\
    (forall final, armv7a_restore_transition abi handler selected after final ->
      final.(ConAssertion.s_mem) = after.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call selected original)
         (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg resumed ** armv7a_task_stack_continuations abi
         resumed.(TskState) resumed.(TskState).(parkedTaskStacks) **
        (unmap_table_rep sg ** frame))) final).
Proof.
  intros external platform port abi sg original suspended focus payload Hbinding Hcall Hslice
    returned after handler frame [node [Hnode [Hgeneration Hsp]]] Hcurrent Haddress Hworld resumed.
  assert (Horiginal_lease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { destruct Hbinding as [Hlength Hlease]; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  rewrite Horiginal_lease in Hnode, Hgeneration.
  match type of Hworld with ?P after =>
    assert (Hopen : P |-- coq_prop (kernel_client_call_stack_facts focus payload returned) &&
      (UCOS2_inv sg returned ** armv7a_task_call_stacks abi returned.(TskState) focus
        returned.(TskState).(parkedTaskStacks) **
       (interrupt_platform_running platform handler.(os_int_exit_invocation)
          handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
        (unmap_table_rep sg ** frame))))
  end.
  { unfold kernel_client_call_stack_world.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen after Hworld) as [[Hcoverage Hlookup] Hheap].
  unfold payload in Hlookup; rewrite Horiginal_lease in Hlookup.
  destruct (armv7a_irq_wrapper_take_call_stack external platform port abi sg returned focus
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) node _ after
    Hcurrent Hnode Hgeneration Hlookup eq_refl Haddress Hcoverage Hheap)
    as [selected [Hpointers [Hreads [Hfocused [Hlease [Hfragments [Hcovered Hresources]]]]]]].
  assert (Hselected_sp : selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp)).
  { assert (Hload : KernelHeapObservation.pointer_load
        (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) node.(tcbStkPtr) after).
    { eapply task_stack_framed_live_sp_load; [exact Hnode|exact Haddress|].
      match type of Hheap with ?P after => assert (Horder : P |--
        UCOS2_inv sg returned ** (armv7a_task_call_stacks abi returned.(TskState) focus
          returned.(TskState).(parkedTaskStacks) **
         (interrupt_platform_running platform handler.(os_int_exit_invocation)
            handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
          (unmap_table_rep sg ** frame)))) by entailer!
      end.
      exact (Horder after Hheap). }
    rewrite Hsp in Hload.
    eapply KernelHeapObservation.pointer_load_deterministic; [exact (proj2 Hpointers)|exact Hload]. }
  assert (Hframe : exists rest : Assertion,
    (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
       selected.(armv7a_continuation_fragments) ** rest) after).
  { eexists.
    match type of Hresources with ?P after => assert (Horder : P |--
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      (UCOS2_inv sg resumed ** armv7a_task_stack_continuations abi
         resumed.(TskState) resumed.(TskState).(parkedTaskStacks) **
       armv7a_dormant_continuation abi selected **
       (interrupt_platform_running platform handler.(os_int_exit_invocation)
          handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
        (unmap_table_rep sg ** frame)))) by entailer!
    end.
    exact (Horder after Hresources). }
  destruct Hframe as [rest Hframe].
  destruct (armv7a_same_frame_registers suspended selected rest after Hbinding Hslice
    ltac:(congruence) Hfragments Hselected_sp Hreads Hframe) as [Hcpsr Hregisters].
  exists selected; split; [exact Hpointers|]. split; [exact Hfocused|].
  split; [exact Hlease|]. split; [exact Hselected_sp|]. split; [exact Hcpsr|].
  split; [exact Hregisters|]. split; [exact Hcovered|]. intros final Hrestore.
  match type of Hresources with ?P after => assert (Horder : P |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi selected **
    (UCOS2_inv sg resumed ** armv7a_task_stack_continuations abi
      resumed.(TskState) resumed.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) by entailer!
  end.
  destruct (armv7a_restore_call_resources external platform port abi handler selected original _ after final
    (proj1 Hfocused) Hreads (Horder after Hresources) Hrestore) as [Hmemory Hrestored].
  split; [exact Hmemory|]. rewrite Hcpsr in Hrestored; exact Hrestored.
Qed.

(** A returning IRQ source cut, with the original saved register values
    recovered from its actual bytes. State/source and spatial transport
    come from ONE existing registry trace; no independent existential
    trace is substituted. The final selection guard identifies a genuine
    return branch, not a claim that every handler returns to this task. *)
Lemma task_create_registered_call_stack_restore : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port)
  extra_resources extra_step extra_effect clients sg original suspended,
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  @kernel_client_call_stack_extension_valid external platform port Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp)) ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg
    original.(os_sched_call_invocation) None extra_effect ->
  forall cut before after state handler (frame : Assertion),
  UCOS2_state_inv sg state ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  kernel_client_heap_trace extra_step sg cut before KernelClientHeapClosed after ->
  kernel_client_heap_observer_cut original.(os_sched_call_invocation) cut ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace external port clients sg original.(os_sched_call_invocation)
      None original.(os_sched_call_origin) state stopped returned_origin returned /\
    (returned.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
     tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
       task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
     let resumed := os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack) in
     exists selected,
       armv7a_irq_restore_pointer_reads sg after
         (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
         selected.(armv7a_continuation_sp) /\
       armv7a_continuation_focus_binding focus selected /\
       selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
       selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
       selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
       selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
       task_stack_live_coverage resumed.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) /\
       (forall final, armv7a_restore_transition abi handler selected after final ->
         final.(ConAssertion.s_mem) = after.(ConAssertion.s_mem) /\
         (kernel_call_execution_owned external platform
            (armv7a_continuation_resumed_call selected original)
            (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) **
          task_stack_fragments_rep handler.(os_int_exit_handler_stack)
            handler.(os_int_exit_handler_fragments) **
          (UCOS2_inv sg resumed ** armv7a_task_stack_continuations abi
            resumed.(TskState) resumed.(TskState).(parkedTaskStacks) **
           (unmap_table_rep sg ** frame))) final)).
Proof.
  intros external platform port Extra abi extra_resources extra_step extra_effect clients sg original suspended
    focus payload Hbinding Hcall Hslice Hspatial Hextra Henter Hexit Hpublish Hsource
    cut before after state handler frame Hvalid Hpointer Htrace Hcut Hpre.
  destruct (kernel_client_call_stack_trace_source_resources external platform port Extra abi
    extra_resources focus payload extra_step extra_effect clients sg original.(os_sched_call_invocation)
    None Hspatial Henter Hexit Hpublish Hsource cut before KernelClientHeapClosed after _
    Htrace state original.(os_sched_call_origin) Hcut Hpre)
    as [returned [stopped [returned_origin [Hstates [Hsources [Hclosed Hworld]]]]]].
  destruct (kernel_client_trace_preserves_saved_pointer Extra extra_effect sg
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hextra
    cut state KernelClientHeapClosed returned Hstates Hvalid Hpointer)
    as [Hreturned Hpointer_returned].
  exists returned, stopped, returned_origin; split; [exact Hstates|].
  split; [exact Hsources|]. intros Hcurrent Haddress resumed.
  exact (task_create_pending_call_stack_restore external platform port abi sg original suspended
    Hbinding Hcall Hslice returned after handler frame Hpointer_returned Hcurrent Haddress Hworld).
Qed.
(** Consume that actual returned heap, finish Restore's BX, then execute
    the next real MRS/CPSID/DSB/BX. The IRQ's current map is used throughout;
    the pre-interruption map is not framed across the handler. Register
    joins below identify the real consecutive instruction cursors. This
    covers an uninterrupted next Save, not an assertion that no further
    IRQ or other-task execution is possible. *)
Lemma task_create_restored_call_next_save : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original selected state written cursor irq_return final_cursor c_return
  registers final_registers acquired after (frame : Assertion),
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) ->
  cursor.(kernel_restore_msr_word) = Some written ->
  cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask written ->
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected original)
     (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   (UCOS2_inv sg state ** task_tcb_init_stack_covered_capsules environment state ** frame)) irq_return ->
  armv7a_restore_suffix_transition restore cursor irq_return final_cursor c_return ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask written ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state c_return
    final_registers acquired after ->
  task_tcb_init_stack_same_call (armv7a_continuation_resumed_call selected original) original /\
  final_cursor.(kernel_restore_return_word) = Some selected.(armv7a_continuation_lr) /\
  kernel_call_save_uninterrupted_execution arch registers state c_return
    final_registers acquired after /\
  (task_tcb_init_stack_covered_save_post environment critical sg
     (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask written)
     final_registers.(kernel_save_r0) state ** frame) after.
Proof.
  intros environment critical arch restore save sg original selected state written cursor
    irq_return final_cursor c_return registers final_registers acquired after frame
    Horigin Hlease Hcoverage Hword Hlr Hmask Howned Hrestore Hregisters Hvalid Hregistermask Hsave.
  rewrite Hmask in Howned.
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call selected original) written cursor irq_return final_cursor c_return
    _ Hword Howned Hrestore) as [Hcursor [Hmemory Hreturned]].
  assert (Hcovered : task_stack_live_coverage state.(TskState)
    (task_stack_call_active_key (armv7a_continuation_resumed_call selected original))).
  { unfold task_stack_call_active_key, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin]; rewrite Horigin; exact Hcoverage. }
  match type of Hreturned with ?P c_return => assert (Hinput : P |--
    task_tcb_init_stack_covered_save_input environment critical sg
      (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask written) state ** frame)
  end.
  { unfold task_tcb_init_stack_covered_save_input, critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  split.
  { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; auto. }
  split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - exact (task_tcb_init_stack_covered_uninterrupted_save environment critical arch save sg
      (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask written)
      state registers c_return final_registers acquired after frame Hregisters Hvalid Hregistermask
      (Hinput c_return Hreturned) Hsave).
Qed.

(** This is the connected source branch consumed at the next acquisition:
    registered client execution -> actual wrapper frame take/restore ->
    Restore BX -> the next local Save. The current map, original CPSR and
    full register contents all come from the same trace and saved buffer.
    Switching to another task is not called a C return; the actual final
    current-task test below selects only the original-call return case. *)
Lemma task_create_registered_restore_next_save : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg original suspended,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None extra_effect ->
  forall cut before after state handler (frame : Assertion),
  UCOS2_state_inv sg state ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  kernel_client_heap_trace extra_step sg cut before KernelClientHeapClosed after ->
  kernel_client_heap_observer_cut original.(os_sched_call_invocation) cut ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
   (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg original.(os_sched_call_invocation)
      None original.(os_sched_call_origin) state stopped returned_origin returned /\
    (returned.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
     tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
       task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
     let resumed := os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack) in
     exists selected,
       armv7a_irq_restore_pointer_reads sg after
         (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
         selected.(armv7a_continuation_sp) /\
       armv7a_continuation_focus_binding focus selected /\
       selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
       selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
       selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
       (forall irq_return written cursor final_cursor c_return registers final_registers acquired final,
         armv7a_restore_transition abi handler selected after irq_return ->
         cursor.(kernel_restore_msr_word) = Some written ->
         cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
         armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask written ->
         armv7a_restore_suffix_transition restore cursor irq_return final_cursor c_return ->
         registers.(kernel_save_return_word) = None ->
         valid_os_cpu_sr registers.(kernel_save_cpsr) ->
         armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask written ->
         armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) resumed c_return
           final_registers acquired final ->
         task_tcb_init_stack_same_call (armv7a_continuation_resumed_call selected original) original /\
         final_cursor.(kernel_restore_return_word) = Some selected.(armv7a_continuation_lr) /\
         kernel_call_save_uninterrupted_execution arch registers resumed c_return
           final_registers acquired final /\
         (task_tcb_init_stack_covered_save_post environment critical sg
            (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask written)
            final_registers.(kernel_save_r0) resumed **
          (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
             handler.(os_int_exit_handler_fragments) ** unmap_table_rep sg ** frame)) final)).
Proof.
  intros environment critical arch Extra restore save extra_resources extra_step extra_effect sg original
    suspended abi focus payload Horigin Hbinding Hcall Hslice Hspatial Hextra Henter Hexit Hpublish Hsource
    cut before after state handler frame Hvalid Hpointer Htrace Hcut Hpre.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources
    extra_step extra_effect critical.(critical_region_clients) sg original suspended
    Hbinding Hcall Hslice Hspatial Hextra Henter Hexit Hpublish Hsource cut before after state
    handler frame Hvalid Hpointer Htrace Hcut Hpre)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hcurrent Haddress resumed.
  destruct (Hreturn Hcurrent Haddress) as [selected [Hpointers [Hfocus [Hlease [Hsp [Hcpsr
    [Hregisters [Hcoverage Hresume]]]]]]]].
  exists selected; split; [exact Hpointers|]. split; [exact Hfocus|]. split; [exact Hsp|].
  split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros irq_return written cursor final_cursor c_return registers final_registers acquired final
    Hirq_restore Hword Hlr Hmask Hrestore Hnone Hregisters_valid Hregisters_mask Hsave.
  destruct (Hresume irq_return Hirq_restore) as [Hmemory Howned].
  match type of Howned with ?P irq_return => assert (Horder : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected original)
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
    (UCOS2_inv sg resumed ** task_tcb_init_stack_covered_capsules environment resumed **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** unmap_table_rep sg ** frame)))
  end.
  { rewrite Hcpsr; unfold task_tcb_init_stack_covered_capsules; entailer!. }
  eapply task_create_restored_call_next_save; try eassumption.
  - rewrite Hcpsr; exact Hmask.
  - exact (Horder irq_return Howned).
Qed.
