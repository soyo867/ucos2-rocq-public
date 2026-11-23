Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual first-level IRQ source segments with the six-field Flag world.
    The same real save, physical counter/SP stores, parked entry, selected
    take and restore transitions supply the resources at their own cuts.
    Current/key/geometry/coverage premises are unchanged. No readiness or
    clean-registration fact is added, and IRQ descriptors do not acquire
    Scheduler's PC=LR or saved-mask=192 restrictions.

    The handler execution is separate from the interrupted local owner.
    These segments do not frame across the intervening handler/registry
    interval, prove first public API entry, or establish a whole IRQ/API. *)

(** Retain the actual local through the real save and park it with
    that same descriptor after the physical nesting/SP writes. *)
Lemma kernel_irq_save_continuation_fields_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler descriptor publication
  (local : Armv7aContinuation -> Assertion) (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice descriptor ->
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
    descriptor.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    descriptor.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre external platform handler **
   (UCOS2_fields_inv sg entry **
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) ** local descriptor ** frame)) before ->
  armv7a_save_transition abi handler descriptor before saved_heap ->
  exists final,
    descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
    kernel_heap_writes (armv7a_continuation_save_writes descriptor)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) descriptor.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_fields_inv sg parked **
     store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
       parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler descriptor publication local frame before saved_heap
    call parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler descriptor before saved_heap Hsave)
    as [Hsource [Hcall [Hbinding [Hmask [Hpc [Hsavedsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler descriptor call _ before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsavedsp Hfragments Hpre Hsave) as [Hwrites Hsaved].
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node descriptor.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      descriptor.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hmap : parked.(TskState).(parkedTaskStacks) =
    task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      descriptor.(armv7a_continuation_fragments)) by (rewrite Htasks; reflexivity).
  assert (Hlive : task_stack_live_sp parked.(TskState) (task_stack_key call.(os_sched_call_stack))
    descriptor.(armv7a_continuation_sp)).
  { intros current Hlookup Hcurrentgen; rewrite Htasks in Hlookup.
    cbn [task_stack_key fst glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask] in Hlookup.
    rewrite Z.eqb_refl in Hlookup; injection Hlookup as Hlookup; subst current; reflexivity. }
  assert (Hreindex :
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
      entry.(TskState).(parkedTaskStacks)).
  { rewrite Htasks.
    exact (kernel_saved_continuation_map_save_sp external platform port abi entry.(TskState) node
      descriptor.(armv7a_continuation_sp) call.(os_sched_call_stack) local
      entry.(TskState).(parkedTaskStacks) Hnode Hgen Hnone). }
  assert (Hentry : armv7a_dormant_continuation abi descriptor ** local descriptor |--
    kernel_saved_continuation_entry abi parked.(TskState) local
      (task_stack_key call.(os_sched_call_stack))
      (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments))).
  { unfold kernel_saved_continuation_entry; Exists descriptor.
    unfold armv7a_task_continuation_resource; rewrite Hcall, <- Hstack; entailer!. }
  assert (Hattach : armv7a_dormant_continuation abi descriptor ** local descriptor **
      store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
        entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
      parked.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic Hreindex; sep_apply_l_atomic Hentry; rewrite Hmap.
    apply store_parked_continuations_park; exact Hnone. }
  match type of Hsaved with ?P saved_heap => assert (Hsplit : P |--
    (UCOS2_fields_inv sg entry **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
        descriptor.(armv7a_continuation_fragments)) **
    (armv7a_dormant_continuation abi descriptor ** local descriptor **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) **
     interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)) end.
  { change (call.(os_sched_call_stack) = descriptor.(armv7a_continuation_stack)) in Hstack.
    rewrite Hstack; entailer!. }
  destruct (Hsplit saved_heap Hsaved) as [owned [rest [Hjoin [Howned Hrest]]]].
  destruct (armv7a_irq_live_entry_fields_parks_stack sg entry node descriptor.(armv7a_continuation_sp)
    call descriptor.(armv7a_continuation_fragments) publication owned Hrunning Hnesting Hcurrent Hnode
    Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Howned)
    as [written [Hrun Hwritten]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  assert (Hclose : UCOS2_fields_inv sg parked **
    (armv7a_dormant_continuation abi descriptor ** local descriptor **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) **
     interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame) |--
    UCOS2_fields_inv sg parked **
    store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
      parked.(TskState).(parkedTaskStacks) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)).
  { sepcon_assoc_change; sep_apply_l_atomic Hattach; entailer!. }
  exists final; split; [exact Hcall|]. split; [exact Hpc|]. split; [exact Hmask|].
  split; [exact Hwrites|]. split; [exact Hwhole|].
  split; [eapply armv7a_irq_live_parked_stack_coverage; eassumption|].
  apply (Hclose final); exists written, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** Read the actual current pointer and saved SP, then take the
    physical bytes and exact dormant/local entry from one map. *)
Lemma task_tcb_init_irq_take_fields_resources : forall external platform port
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
  (UCOS2_fields_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
     state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot))
    suspended.(armv7a_continuation_sp) /\
  armv7a_continuation_restore_reads suspended heap /\
  task_stack_live_coverage restored.(TskState) (Some (task_stack_key suspended.(armv7a_continuation_stack))) /\
  (UCOS2_fields_inv sg restored ** store_parked_continuations
     (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
     restored.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended ** frame) heap.
Proof.
  intros external platform port abi sg state saved_local suspended call node frame heap
    Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre restored.
  assert (Hpointers : armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) node.(tcbStkPtr)).
  { match type of Hpre with ?P heap => assert (Horder : P |-- UCOS2_fields_inv sg state **
      (store_parked_continuations
        (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
        state.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
    destruct (Horder heap Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_fields_live; eassumption. }
  match type of Hpre with ?P heap => assert (Htake : P |--
    coq_prop (armv7a_continuation_binding suspended /\ armv7a_task_frame_slice suspended /\
      task_stack_live_sp state.(TskState) (task_stack_key suspended.(armv7a_continuation_stack))
        suspended.(armv7a_continuation_sp)) &&
    (UCOS2_fields_inv sg restored ** store_parked_continuations
       (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
       restored.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
       suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended ** frame)) end.
  { rewrite UCOS2_fields_inv_split_parked_stacks; Intros.
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
    sep_apply_l_atomic (UCOS2_fields_inv_merge_updated_parked_stacks sg state _ Hvalid Hconsistent).
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
      (UCOS2_fields_inv sg restored ** store_parked_continuations
         (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
         restored.(TskState).(parkedTaskStacks) ** armv7a_dormant_continuation abi suspended ** frame))
      by entailer! end.
    exact (Horder heap Hresources).
  - split; [apply task_stack_take_covers_selected; exact Hcoverage|exact Hresources].
Qed.

(** The real IRQ save produces Some call, PC and mask observations.
    The already owned interrupted local is deposited once. *)
Lemma flag_source_fields_irq_save_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler descriptor publication saved_local
  (interrupted_local frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice descriptor ->
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
    descriptor.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    descriptor.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre external platform handler **
   (UCOS2_fields_inv sg entry **
    store_parked_continuations
      (kernel_saved_continuation_entry abi entry.(TskState) (task_create_continuation_local saved_local))
      entry.(TskState).(parkedTaskStacks) ** interrupted_local ** frame)) before ->
  armv7a_save_transition abi handler descriptor before saved_heap ->
  exists final,
    descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
    kernel_heap_writes (armv7a_continuation_save_writes descriptor)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) descriptor.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_fields_inv sg parked **
     store_parked_continuations
       (kernel_saved_continuation_entry abi parked.(TskState)
         (flag_source_irq_local saved_local descriptor interrupted_local))
       parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler descriptor publication saved_local interrupted_local
    frame before saved_heap call parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler descriptor before saved_heap Hsave)
    as [Hsource [Hcall [Hbinding Hobservations]]].
  assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hstack; rewrite Hcall in Hstack; symmetry; exact Hstack. }
  assert (Habsent : entry.(TskState).(parkedTaskStacks)
    (task_stack_key descriptor.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  match type of Hpre with ?P before => assert (Hopen : P |--
    os_int_exit_frame_save_pre external platform handler **
      (UCOS2_fields_inv sg entry **
       store_parked_continuations
         (kernel_saved_continuation_entry abi entry.(TskState)
           (flag_source_irq_local saved_local descriptor interrupted_local))
         entry.(TskState).(parkedTaskStacks) **
       flag_source_irq_local saved_local descriptor interrupted_local descriptor ** frame)) end.
  { sep_apply_l_atomic (proj1 (flag_source_irq_map_absent external platform port abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) saved_local descriptor interrupted_local Habsent)).
    sep_apply_r_atomic (proj2 (flag_source_irq_local_selected saved_local descriptor interrupted_local)); entailer!. }
  exact (kernel_irq_save_continuation_fields_resources external platform port abi sg entry node handler descriptor
    publication (flag_source_irq_local saved_local descriptor interrupted_local) frame before saved_heap
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    (Hopen before Hpre) Hsave).
Qed.

(** Extract the same interrupted local before consuming its exact
    selected entry; node ownership is neither copied nor inferred. *)
Lemma flag_source_fields_irq_take_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state saved_local suspended call node
  (interrupted_local frame : Assertion) heap,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_fields_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState)
       (flag_source_irq_local saved_local suspended interrupted_local))
     state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot))
    suspended.(armv7a_continuation_sp) /\
  armv7a_continuation_restore_reads suspended heap /\
  task_stack_live_coverage restored.(TskState) (Some (task_stack_key suspended.(armv7a_continuation_stack))) /\
  (UCOS2_fields_inv sg restored ** store_parked_continuations
     (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
     restored.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
   (interrupted_local ** frame)) heap.
Proof.
  intros external platform port abi sg state saved_local suspended call node interrupted_local frame heap
    Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre restored.
  match type of Hpre with ?P heap => assert (Hopen : P |--
    UCOS2_fields_inv sg state ** store_parked_continuations
      (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
      state.(TskState).(parkedTaskStacks) ** (interrupted_local ** frame)) end.
  { unfold flag_source_irq_local.
    sep_apply_l_atomic (flag_continuation_map_take_node external platform port abi state.(TskState)
      suspended.(armv7a_continuation_stack) interrupted_local (task_tcb_init_irq_local saved_local suspended)
      state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_fragments) Hparked); entailer!. }
  exact (task_tcb_init_irq_take_fields_resources external platform port abi sg state saved_local suspended call node
    (interrupted_local ** frame) heap Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage (Hopen heap Hpre)).
Qed.

(** Consume the actual restore transition and return the original
    local plus the actual last-take absence at the resumed C cut. *)
Lemma flag_source_fields_irq_restore_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state saved_local suspended call node handler
  (interrupted_local frame : Assertion) before after,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_fields_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState)
       (flag_source_irq_local saved_local suspended interrupted_local))
     state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) before ->
  armv7a_restore_transition abi handler suspended before after ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  restored.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) = None /\
  (flag_source_save_input abi (fun sg state => UCOS2_fields_inv sg state)
     (task_create_continuation_local saved_local) sg
     (Some (task_stack_key suspended.(armv7a_continuation_stack)))
     (armv7a_continuation_resumed_call suspended call)
     (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) restored interrupted_local **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port abi sg state saved_local suspended call node handler interrupted_local frame
    before after Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre Hrestore restored.
  destruct (flag_source_fields_irq_take_resources external platform port abi sg state saved_local suspended call node
    interrupted_local _ before Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre)
    as [Hpointers [Hreads [Hcovered Htaken]]].
  fold restored in Hcovered, Htaken.
  match type of Htaken with ?P before => assert (Hopen : P |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
      suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    (UCOS2_fields_inv sg restored ** store_parked_continuations
       (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
       restored.(TskState).(parkedTaskStacks) ** interrupted_local ** frame)) by entailer! end.
  destruct (armv7a_restore_transition_resources external platform port abi handler suspended _ before after
    Hreads (Hopen before Htaken) Hrestore) as [Hmemory Hafter].
  rewrite Hcall in Hafter.
  split; [exact Hmemory|]. split.
  - unfold restored, os_int_exit_wrapper_restored_state;
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup.
  - match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold flag_source_save_input, kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
    exact (Hclose after Hafter).
Qed.

