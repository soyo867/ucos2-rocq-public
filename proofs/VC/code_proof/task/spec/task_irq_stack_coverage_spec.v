Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_frame_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma armv7a_irq_live_parked_stack_coverage : forall entry node call sp fragments,
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  task_stack_live_coverage (armv7a_irq_live_parked_state entry call sp fragments).(TskState) None.
Proof.
  intros entry node call sp fragments Hnode Hcoverage.
  unfold armv7a_irq_live_parked_state; cbn [replace_TskS TskState].
  apply task_stack_park_covers_active.
  unfold armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state.
  destruct entry.(SchedState).(isRunning); unfold os_sched_save_current_sp;
    cbn [replace_IntrS TskState]; rewrite Hnode;
    cbn [replace_TskS TskState]; eapply task_stack_save_sp_preserves_coverage; eassumption.
Qed.

(** The same first-level live-task counter/SP producer, now retaining the
    strong map. The other entries are transported using actual unchanged
    generation/SP fields; the newly parked entry gets its SP from the real
    TCB store. A dormant CPU authority is consumed, never manufactured from
    a frame image or task identifier. *)
Lemma armv7a_irq_live_entry_covers_stacks : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node saved call publication (frame : Assertion) heap,
  saved.(armv7a_continuation_call) = Some call ->
  armv7a_continuation_binding saved -> armv7a_task_frame_slice saved ->
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
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_inv sg entry **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
   armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame) heap ->
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  exists final,
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_inv sg parked **
     armv7a_task_stack_continuations abi parked.(TskState) parked.(TskState).(parkedTaskStacks) ** frame) final.
Proof.
  intros external platform port abi sg entry node saved call publication frame heap Hcall Hbinding
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication
    Hsp Hcoverage Hpre parked.
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node saved.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hmap : parked.(TskState).(parkedTaskStacks) =
    task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      saved.(armv7a_continuation_fragments)) by (rewrite Htasks; reflexivity).
  assert (Hlive : task_stack_live_sp parked.(TskState) (task_stack_key saved.(armv7a_continuation_stack))
    saved.(armv7a_continuation_sp)).
  { rewrite <- Hstack; intros current Hlookup Hcurrentgen.
    rewrite Htasks in Hlookup.
    cbn [task_stack_key fst glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask] in Hlookup.
    rewrite Z.eqb_refl in Hlookup; injection Hlookup as Hlookup; subst current; reflexivity. }
  assert (Hreindex : armv7a_task_stack_continuations abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi parked.(TskState) entry.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic (armv7a_task_stack_continuations_save_sp external platform port abi
      entry.(TskState) node saved.(armv7a_continuation_sp) call.(os_sched_call_stack)
      entry.(TskState).(parkedTaskStacks) Hnode Hgen Hnone).
    apply armv7a_task_stack_continuations_used_map_eq; rewrite Htasks; reflexivity. }
  assert (Hentry : armv7a_dormant_continuation abi saved |--
    armv7a_task_stack_entry abi parked.(TskState) (task_stack_key call.(os_sched_call_stack))
      (call.(os_sched_call_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { unfold armv7a_task_stack_entry; Exists saved.
    unfold armv7a_task_continuation_resource; rewrite Hcall, Hstack; entailer!. }
  assert (Hattach : armv7a_dormant_continuation abi saved **
      armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi parked.(TskState) parked.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic Hreindex; sep_apply_l_atomic Hentry.
    unfold armv7a_task_stack_continuations; rewrite Hmap.
    apply store_parked_continuations_park; exact Hnone. }
  assert (Hsplit : UCOS2_inv sg entry **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
      armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame |--
    (UCOS2_inv sg entry ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments)) **
    (armv7a_dormant_continuation abi saved **
     armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame)).
  { rewrite Hstack; entailer!. }
  destruct (Hsplit heap Hpre) as [owned [rest [Hjoin [Howned Hrest]]]].
  destruct (armv7a_irq_live_entry_parks_stack sg entry node saved.(armv7a_continuation_sp)
    call saved.(armv7a_continuation_fragments) publication owned Hrunning Hnesting Hcurrent Hnode
    Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Howned)
    as [updated [Hrun Hupdated]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  split; [eapply armv7a_irq_live_parked_stack_coverage; eassumption|].
  assert (Hmerge : UCOS2_inv sg parked **
      (armv7a_dormant_continuation abi saved **
       armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_inv sg parked **
      armv7a_task_stack_continuations abi parked.(TskState) parked.(TskState).(parkedTaskStacks) ** frame).
  { assert (Horder : UCOS2_inv sg parked **
        (armv7a_dormant_continuation abi saved **
         armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame) |--
      (armv7a_dormant_continuation abi saved **
       armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks)) **
      (UCOS2_inv sg parked ** frame)) by entailer!.
    intros whole Hheap.
    destruct (Horder whole Hheap) as [caps [other [Hjoined [Hcaps Hother]]]].
    assert (Hattached : (armv7a_task_stack_continuations abi parked.(TskState)
        parked.(TskState).(parkedTaskStacks) ** (UCOS2_inv sg parked ** frame)) whole).
    { exists caps, other; split; [exact Hjoined|].
      split; [exact (Hattach caps Hcaps)|exact Hother]. }
    assert (Hfinish : armv7a_task_stack_continuations abi parked.(TskState)
        parked.(TskState).(parkedTaskStacks) ** (UCOS2_inv sg parked ** frame) |--
      UCOS2_inv sg parked ** armv7a_task_stack_continuations abi parked.(TskState)
        parked.(TskState).(parkedTaskStacks) ** frame) by entailer!.
    exact (Hfinish whole Hattached). }
  apply (Hmerge final); exists updated, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** First-level IRQ entry on an already running task. The 16-word slice
    below is an owned part of the original caller's stack, not a supplied
    postcondition. Its contents are computed by the five source store
    groups and matched to the SAME ABI save event by memory determinism.
    Only that event exchanges CPU authority; the byte proof alone never
    produces a dormant continuation. Prefix, suffix, borrowed holes and
    the arbitrary caller frame retain their existing ownership. *)
Lemma armv7a_irq_source_save_covers_stacks : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler publication sp cpsr registers lr pc prefix suffix first old_words
  (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (cpsr :: registers ++ [lr; pc]))] ++ suffix in
  let saved := armv7a_irq_save_image call sp cpsr registers lr pc fragments in
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 -> 0 <= pc < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  sp = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
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
    call.(os_sched_call_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) sp ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre external platform handler **
    (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi
      entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  let parked := armv7a_irq_live_parked_state entry call sp fragments in
  exists final,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    armv7a_continuation_restore_reads saved saved_heap /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) sp) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_inv sg parked ** armv7a_task_stack_continuations abi
      parked.(TskState) parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler publication sp cpsr registers lr pc
    prefix suffix first old_words frame before saved_heap call fragments saved
    Hlength Hcpsr Hlr Hpc_range Hranges Hold Hposition Hrunning Hnesting Hcurrent Hnode
    Hid Hgen Hnone Haddress Hregion Hbounds Hpublication Hsp Hcoverage Hpre Hsave parked.
  set (residual := interrupt_platform_running platform call.(os_sched_call_invocation)
      call.(os_sched_call_origin) handler.(os_int_exit_interrupted_mask) **
    external.(os_sched_arch_running) call **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) **
    (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi
      entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame)).
  assert (Howned : os_int_exit_frame_save_pre external platform handler **
      (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi
        entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame) |--
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) ** residual).
  { unfold os_int_exit_frame_save_pre, kernel_call_execution_owned, os_sched_context_resources.
    fold call; rewrite Hold; unfold residual; entailer!. }
  destruct (armv7a_irq_save_fragment_execution call sp cpsr registers lr pc prefix suffix first
    old_words residual before Hlength Hcpsr Hlr Hpc_range Hranges Hposition (Howned before Hpre))
    as [written_heap [Hphysical [Hwritten [Hreads Hslice]]]].
  fold fragments saved in Hphysical, Hwritten, Hreads, Hslice.
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hmask [Hpc [Hsavedsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler saved call _ before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsavedsp Hfragments Hpre Hsave) as [Hwrites Hsaved].
  assert (Hmemory : written_heap.(ConAssertion.s_mem) = saved_heap.(ConAssertion.s_mem)).
  { eapply kernel_heap_writes_deterministic; [exact (proj1 Hphysical)|exact Hwrites]. }
  assert (Hactual_reads : armv7a_continuation_restore_reads saved saved_heap).
  { destruct Hreads as [Hbind Hwords]; split; [exact Hbind|].
    revert Hwords.
    generalize (armv7a_continuation_sp saved).
    induction (armv7a_continuation_words saved) as [|word rest IH]; intros address Hwords;
      cbn in *; [exact I|].
    destruct Hwords as [Hword Hrest]; split; [|apply IH; exact Hrest].
    unfold KernelHeapObservation.pointer_load in *; rewrite <- Hmemory; exact Hword. }
  assert (Hgeometry : task_stack_fragments_in_range
    call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments)).
  { change (task_stack_fragments_in_range
      call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments).
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hold; exact Hbounds. }
  assert (Hreorder :
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi
      entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_inv sg entry ** task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)) by entailer!.
  destruct (armv7a_irq_live_entry_covers_stacks external platform port abi sg entry node saved call
    publication _ saved_heap Hcall Hbinding Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Hreorder saved_heap Hsaved))
    as [final [Hrun [Hcovered Hpost]]].
  exists final; split; [exact Hwrites|]. split; [exact Hactual_reads|].
  split; [exact Hrun|]. split; assumption.
Qed.

(** The wrapper's actual current-TCB and saved-SP reads select one entry
    from the same strong map. The generation check connects the concrete
    TCB SP to that entry, so all sixteen restore reads follow from owned
    bytes, not a new platform assumption. This does not identify an
    arbitrary selected invocation with the earlier interrupted caller. *)
Lemma armv7a_irq_wrapper_take_covered_stack : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state incoming fragments
  node (frame : Assertion) heap,
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_task_stack_continuations abi
    state.(TskState) state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let restored := os_int_exit_wrapper_restored_state state incoming in
  exists saved,
    armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads saved heap /\
    saved.(armv7a_continuation_stack) = incoming /\
    saved.(armv7a_continuation_fragments) = fragments /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
    (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
      restored.(TskState) restored.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi saved ** frame) heap.
Proof.
  intros external platform port abi sg state incoming fragments node frame heap
    Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre restored.
  assert (Horder : UCOS2_inv sg state ** armv7a_task_stack_continuations abi
      state.(TskState) state.(TskState).(parkedTaskStacks) ** frame |--
    UCOS2_inv sg state ** (armv7a_task_stack_continuations abi
      state.(TskState) state.(TskState).(parkedTaskStacks) ** frame)) by entailer!.
  assert (Hpointers : armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr)).
  { destruct (Horder heap Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_live; eassumption. }
  assert (Htake : UCOS2_inv sg state ** armv7a_task_stack_continuations abi
      state.(TskState) state.(TskState).(parkedTaskStacks) ** frame |--
    EX saved,
      coq_prop (armv7a_continuation_binding saved /\
        saved.(armv7a_continuation_stack) = incoming /\
        saved.(armv7a_continuation_fragments) = fragments /\
        armv7a_task_frame_slice saved /\
        task_stack_live_sp state.(TskState) (task_stack_key incoming) saved.(armv7a_continuation_sp)) &&
      (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
        restored.(TskState) restored.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
         saved.(armv7a_continuation_fragments) **
       armv7a_task_continuation_resource abi saved ** frame)).
  { sep_apply_l_atomic (os_int_exit_wrapper_take_destination_resources sg state incoming fragments Hparked).
    unfold armv7a_task_stack_continuations.
    sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_stack_entry abi state.(TskState))
      state.(TskState).(parkedTaskStacks) incoming fragments Hparked).
    unfold armv7a_task_stack_entry at 1; Intros saved.
    assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
      saved.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), fragments)) by tauto.
    assert (Hlease : saved.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct saved.(armv7a_continuation_stack), incoming;
        cbn in *; congruence. }
    assert (Hfragments : saved.(armv7a_continuation_fragments) = fragments) by congruence.
    Exists saved; unfold restored, os_int_exit_wrapper_restored_state.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    rewrite Hlease, Hfragments; entailer!. }
  destruct (Htake heap Hpre) as [saved [[Hbinding [Hlease [Hfragments [Hslice Hsp]]]] Hresources]].
  assert (Hnode_sp : node.(tcbStkPtr) = saved.(armv7a_continuation_sp)).
  { apply Hsp; assumption. }
  assert (Hreads : armv7a_continuation_restore_reads saved heap).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    assert (Hframe : UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
        restored.(TskState) restored.(TskState).(parkedTaskStacks) **
        task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
          saved.(armv7a_continuation_fragments) **
        armv7a_task_continuation_resource abi saved ** frame |--
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
        restored.(TskState) restored.(TskState).(parkedTaskStacks) **
       armv7a_task_continuation_resource abi saved ** frame)) by entailer!.
    exact (Hframe heap Hresources). }
  exists saved; rewrite Hnode_sp in Hpointers.
  split; [exact Hpointers|]. split; [exact Hreads|]. split; [exact Hlease|].
  split; [exact Hfragments|].
  split; [apply task_stack_take_covers_selected; exact Hcoverage|exact Hresources].
Qed.

(** Concrete no-scheduling OSIntExit path followed by the wrapper reads
    and one resource take. This composes an existing C memory producer;
    it does not declare the BSP body empty or require its output to equal
    its earlier input. Switching/selection paths have separate producers. *)
Lemma armv7a_irq_no_schedule_takes_covered_stack : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state incoming fragments
  node (frame : Assertion) heap,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_task_stack_continuations abi
    state.(TskState) state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let returned := os_int_exit_counter_state state.(SchedState).(isRunning) state in
  let restored := os_int_exit_wrapper_restored_state returned incoming in
  exists final saved,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    armv7a_irq_restore_pointer_reads sg final (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads saved final /\
    saved.(armv7a_continuation_stack) = incoming /\
    saved.(armv7a_continuation_fragments) = fragments /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
    (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
      restored.(TskState) restored.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi saved ** frame) final.
Proof.
  intros external platform port abi sg state incoming fragments node frame heap
    Hbranch Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre returned restored.
  assert (Horder : UCOS2_inv sg state ** armv7a_task_stack_continuations abi
      state.(TskState) state.(TskState).(parkedTaskStacks) ** frame |--
    UCOS2_inv sg state ** (armv7a_task_stack_continuations abi
      state.(TskState) state.(TskState).(parkedTaskStacks) ** frame)) by entailer!.
  destruct (os_int_exit_masked_no_schedule_frame_post sg state _ heap Hbranch (Horder heap Hpre))
    as [final [Hrun Hpost]].
  assert (Hafter : (UCOS2_inv sg returned ** armv7a_task_stack_continuations abi
    returned.(TskState) returned.(TskState).(parkedTaskStacks) ** frame) final).
  { assert (Hassoc : UCOS2_inv sg returned ** (armv7a_task_stack_continuations abi
        state.(TskState) state.(TskState).(parkedTaskStacks) ** frame) |--
      UCOS2_inv sg returned ** armv7a_task_stack_continuations abi
        returned.(TskState) returned.(TskState).(parkedTaskStacks) ** frame).
    { unfold returned, os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
    exact (Hassoc final Hpost). }
  destruct (armv7a_irq_wrapper_take_covered_stack external platform port abi sg returned incoming
    fragments node frame final Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hafter)
    as [saved Hsaved].
  exists final, saved; split; assumption.
Qed.
