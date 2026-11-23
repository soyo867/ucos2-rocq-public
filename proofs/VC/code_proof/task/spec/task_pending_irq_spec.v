Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_save_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** IRQ entry may save a running creator while an earlier call is already
    parked. Retain the earlier focus when adding the newly saved owner.
    The existing interrupted-call producer establishes its own focus too;
    determinism identifies the SAME concrete endpoint for both proofs.

    Keep the new descriptor outside the earlier map as a joint split view,
    so restoring it need not forget the earlier focus. The two merged maps
    are alternative views of that SAME heap, not duplicated ownership.
    Handler steps still have to preserve the required resources on their
    actual execution before the return consumer below can use them. *)
Lemma armv7a_irq_live_entry_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node saved call publication focus payload (frame : Assertion) heap,
  saved.(armv7a_continuation_call) = Some call ->
  armv7a_continuation_binding saved -> armv7a_task_frame_slice saved ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
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
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) heap ->
  let interrupted := armv7a_call_focus call saved.(armv7a_continuation_pc) saved.(armv7a_continuation_lr) in
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  exists final,
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload /\
    (UCOS2_inv sg parked ** armv7a_dormant_continuation abi saved **
     armv7a_task_call_stacks abi parked.(TskState) focus
       (task_stack_take parked.(TskState).(parkedTaskStacks)
         saved.(armv7a_continuation_stack)) ** frame) final /\
    (UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
      parked.(TskState).(parkedTaskStacks) ** frame) final /\
    (UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) interrupted
      parked.(TskState).(parkedTaskStacks) ** frame) final.
Proof.
  intros external platform port abi sg entry node saved call publication focus payload frame heap Hcall Hbinding
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry Hpublication
    Hsp Hcoverage Hpre interrupted parked.
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Hdifferent : task_stack_key call.(os_sched_call_stack) <> armv7a_call_focus_key focus)
    by (intro Heq; rewrite Heq in Hnone; congruence).
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
  assert (Htake_map : task_stack_take parked.(TskState).(parkedTaskStacks)
      saved.(armv7a_continuation_stack) = entry.(TskState).(parkedTaskStacks)).
  { rewrite Hmap, <- Hstack; unfold task_stack_take, task_stack_park_fragments, field_update.
    apply functional_extensionality; intro key.
    destruct task_stack_key_eq_dec as [Heq|Hne]; [subst key; exact (eq_sym Hnone)|reflexivity]. }
  assert (Hretained : parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { rewrite Hmap, task_stack_park_fragments_lookup_other; [exact Hfocus|congruence]. }
  assert (Hlive : task_stack_live_sp parked.(TskState) (task_stack_key saved.(armv7a_continuation_stack))
    saved.(armv7a_continuation_sp)).
  { rewrite <- Hstack; intros current Hlookup Hcurrentgen; rewrite Htasks in Hlookup.
    cbn [task_stack_key fst glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask] in Hlookup.
    rewrite Z.eqb_refl in Hlookup; injection Hlookup as Hlookup; subst current; reflexivity. }
  assert (Hreindex : armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_call_stacks abi parked.(TskState) focus entry.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic (armv7a_task_call_stacks_save_sp external platform port abi
      entry.(TskState) node saved.(armv7a_continuation_sp) call.(os_sched_call_stack) focus
      entry.(TskState).(parkedTaskStacks) Hnode Hgen Hnone).
    apply armv7a_task_call_stacks_used_map_eq; rewrite Htasks; reflexivity. }
  assert (Hentry : armv7a_dormant_continuation abi saved |--
    armv7a_task_call_stack_entry abi parked.(TskState) focus (task_stack_key saved.(armv7a_continuation_stack))
      (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec as [Heq|Hne].
    - rewrite <- Hstack in Heq; contradiction.
    - unfold armv7a_task_stack_entry; Exists saved.
      unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
  assert (Hattach : armv7a_dormant_continuation abi saved **
      armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_call_stacks abi parked.(TskState) focus parked.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic Hreindex; sep_apply_l_atomic Hentry; rewrite Hmap, Hstack.
    unfold armv7a_task_call_stacks; apply store_parked_continuations_park.
    rewrite <- Hstack; exact Hnone. }
  match type of Hpre with ?P heap => assert (Hsplit : P |--
    (UCOS2_inv sg entry ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments)) **
    (armv7a_dormant_continuation abi saved **
     armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite Hstack; entailer!. }
  destruct (Hsplit heap Hpre) as [owned [rest [Hjoin [Howned Hrest]]]].
  destruct (armv7a_irq_live_entry_parks_stack sg entry node saved.(armv7a_continuation_sp)
    call saved.(armv7a_continuation_fragments) publication owned Hrunning Hnesting Hcurrent Hnode
    Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Howned)
    as [updated [Hrun Hupdated]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  assert (Hjoint : (UCOS2_inv sg parked ** armv7a_dormant_continuation abi saved **
    armv7a_task_call_stacks abi parked.(TskState) focus
      (task_stack_take parked.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) ** frame) final).
  { assert (Hmerge : UCOS2_inv sg parked **
      (armv7a_dormant_continuation abi saved **
       armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) |--
      UCOS2_inv sg parked ** armv7a_dormant_continuation abi saved **
      armv7a_task_call_stacks abi parked.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame).
    { sep_apply_l_atomic Hreindex; entailer!. }
    rewrite Htake_map; apply Hmerge; exists updated, rest; split; [exact Hfinal|]; split; assumption. }
  assert (Hwith_old : (UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
      parked.(TskState).(parkedTaskStacks) ** frame) final).
  { assert (Hmerge : UCOS2_inv sg parked **
      (armv7a_dormant_continuation abi saved **
       armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) |--
      UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
        parked.(TskState).(parkedTaskStacks) ** frame).
    { sepcon_assoc_change; sep_apply_l_atomic Hattach; entailer!. }
    apply Hmerge; exists updated, rest; split; [exact Hfinal|]; split; assumption. }
  match type of Hpre with ?P heap => assert (Hforget : P |--
    UCOS2_inv sg entry **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame) end.
  { sep_apply_l_atomic (armv7a_task_call_stacks_forget external platform port abi entry.(TskState)
      focus entry.(TskState).(parkedTaskStacks)); entailer!. }
  destruct (armv7a_irq_live_entry_parks_call external platform port abi sg entry node saved call
    publication frame heap Hcall Hbinding Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Hforget heap Hpre))
    as [same_final [Hsame_run [Hcovered Hwith_interrupted]]].
  assert (Hequal : same_final = final) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst same_final; exists final.
  exact (conj Hwhole (conj Hcovered (conj Hretained (conj Hjoint (conj Hwith_old Hwith_interrupted))))).
Qed.

(** The approved save transition supplies the captured descriptor and PC
    from the very same event whose physical writes precede IRQ entry.
    The earlier focused map is part of that event's disjoint frame. Both
    later identities are established by source producers, not inferred
    from equal pool addresses or assumed as platform OS preservation. *)
Lemma armv7a_irq_source_save_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication focus payload (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  armv7a_task_frame_slice saved ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
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
  (os_int_exit_frame_save_pre external platform handler **
    (UCOS2_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  let interrupted := armv7a_call_focus call handler.(os_int_exit_interrupted_pc)
    saved.(armv7a_continuation_lr) in
  let retained := interrupt_platform_running platform handler.(os_int_exit_invocation)
    handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame in
  exists final,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload /\
    (UCOS2_inv sg parked ** armv7a_dormant_continuation abi saved **
     armv7a_task_call_stacks abi parked.(TskState) focus
       (task_stack_take parked.(TskState).(parkedTaskStacks)
         saved.(armv7a_continuation_stack)) ** retained) final /\
    (UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
      parked.(TskState).(parkedTaskStacks) ** retained) final /\
    (UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) interrupted
      parked.(TskState).(parkedTaskStacks) ** retained) final.
Proof.
  intros external platform port abi sg entry node handler saved publication focus payload frame before saved_heap call
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry Hpublication
    Hsp Hcoverage Hpre Hsave parked interrupted retained.
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hmask [Hpc [Hsavedsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler saved call _ before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsavedsp Hfragments Hpre Hsave) as [Hwrites Hsaved].
  match type of Hsaved with ?P saved_heap => assert (Horder : P |--
    UCOS2_inv sg entry **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** retained)
    by (unfold retained; entailer!) end.
  destruct (armv7a_irq_live_entry_preserves_pending_call external platform port abi sg entry node saved call
    publication focus payload retained saved_heap Hcall Hbinding Hslice Hrunning Hnesting Hcurrent Hnode Hid
    Hgen Hnone Hfocus Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Horder saved_heap Hsaved))
    as [final [Hrun [Hcovered [Hretained [Hjoint [Hold Hnew]]]]]].
  exists final; split; [exact Hwrites|]. split; [exact Hrun|]. split; [exact Hcovered|].
  split; [exact Hretained|]. split; [exact Hjoint|]. split; [exact Hold|].
  unfold interrupted; rewrite <- Hpc; exact Hnew.
Qed.

(** Consume the exact newly saved descriptor from the split producer.
    The wrapper reads the current TCB and its SP, takes that frame's bytes
    once, and the ABI exchanges the handler owner for the selected call.
    The remaining map keeps the earlier caller's focus throughout. *)
Lemma armv7a_irq_wrapper_restore_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg state saved call node handler focus (frame : Assertion) heap,
  armv7a_continuation_binding saved -> armv7a_task_frame_slice saved ->
  saved.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some saved.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(tcbStkPtr) = saved.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key saved.(armv7a_continuation_stack)) =
    Some (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_dormant_continuation abi saved **
   armv7a_task_call_stacks abi state.(TskState) focus
     (task_stack_take state.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  let restored := os_int_exit_wrapper_restored_state state saved.(armv7a_continuation_stack) in
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp) /\
  task_stack_live_coverage restored.(TskState) (Some (task_stack_key saved.(armv7a_continuation_stack))) /\
  (forall final, armv7a_restore_transition abi handler saved heap final ->
    final.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
    (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved call)
       (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     (UCOS2_inv sg restored ** armv7a_task_call_stacks abi restored.(TskState) focus
        restored.(TskState).(parkedTaskStacks) ** frame)) final).
Proof.
  intros external platform port abi sg state saved call node handler focus frame heap
    Hbinding Hslice Hcall Hcurrent Hnode Hsp Hparked Haddress Hcoverage Hpre restored.
  assert (Hpointers : armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp)).
  { match type of Hpre with ?P heap =>
      assert (Horder : P |-- UCOS2_inv sg state **
        (armv7a_dormant_continuation abi saved **
         armv7a_task_call_stacks abi state.(TskState) focus
           (task_stack_take state.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
         (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
          os_int_exit_context_resources port handler ** frame))) by entailer!
    end.
    destruct (Horder heap Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    rewrite <- Hsp; eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_live; eassumption. }
  assert (Hreindex : armv7a_task_call_stacks abi state.(TskState) focus
      (task_stack_take state.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) |--
    armv7a_task_call_stacks abi restored.(TskState) focus restored.(TskState).(parkedTaskStacks)).
  { unfold restored, os_int_exit_wrapper_restored_state; cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply armv7a_task_call_stacks_used_map_eq; reflexivity. }
  match type of Hpre with ?P heap =>
    assert (Htake : P |--
      interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
      (UCOS2_inv sg restored ** armv7a_task_call_stacks abi restored.(TskState) focus
        restored.(TskState).(parkedTaskStacks) ** frame))
  end.
  { sep_apply_l_atomic (os_int_exit_wrapper_take_destination_resources sg state
      saved.(armv7a_continuation_stack) saved.(armv7a_continuation_fragments) Hparked).
    sep_apply_l_atomic Hreindex; entailer!. }
  pose proof (Htake heap Hpre) as Hresources.
  assert (Hreads : armv7a_continuation_restore_reads saved heap).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hresources with ?P heap =>
      assert (Horder : P |--
        task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
          saved.(armv7a_continuation_fragments) **
        (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
         os_int_exit_context_resources port handler ** armv7a_dormant_continuation abi saved **
         (UCOS2_inv sg restored ** armv7a_task_call_stacks abi restored.(TskState) focus
           restored.(TskState).(parkedTaskStacks) ** frame))) by entailer!
    end.
    exact (Horder heap Hresources). }
  split; [exact Hpointers|].
  split; [apply task_stack_take_covers_selected; exact Hcoverage|].
  intros final Hrun; eapply armv7a_restore_call_resources; eassumption.
Qed.

(** The real OSIntExit no-schedule counter branch followed by wrapper
    return. Its frame contains both the exact interrupted descriptor and
    the remaining focused map, so neither identity is recovered from a
    weaker existential map at the return boundary. *)
Lemma armv7a_irq_no_schedule_restore_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg state saved call node handler focus (frame : Assertion) heap,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  armv7a_continuation_binding saved -> armv7a_task_frame_slice saved ->
  saved.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some saved.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) saved.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(tcbStkPtr) = saved.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key saved.(armv7a_continuation_stack)) =
    Some (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_dormant_continuation abi saved **
   armv7a_task_call_stacks abi state.(TskState) focus
     (task_stack_take state.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  let returned := os_int_exit_counter_state state.(SchedState).(isRunning) state in
  let restored := os_int_exit_wrapper_restored_state returned saved.(armv7a_continuation_stack) in
  exists exit_heap,
    os_int_exit_masked_no_schedule_fragment sg heap exit_heap /\
    armv7a_irq_restore_pointer_reads sg exit_heap
      (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp) /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key saved.(armv7a_continuation_stack))) /\
    (forall final, armv7a_restore_transition abi handler saved exit_heap final ->
      final.(ConAssertion.s_mem) = exit_heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved call)
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg restored ** armv7a_task_call_stacks abi restored.(TskState) focus
          restored.(TskState).(parkedTaskStacks) ** frame)) final).
Proof.
  intros external platform port abi sg state saved call node handler focus frame heap Hbranch
    Hbinding Hslice Hcall Hcurrent Hnode Hsp Hparked Haddress Hcoverage Hpre returned restored.
  match type of Hpre with ?P heap =>
    assert (Horder : P |-- UCOS2_inv sg state **
      (armv7a_dormant_continuation abi saved **
       armv7a_task_call_stacks abi state.(TskState) focus
         (task_stack_take state.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** frame))) by entailer!
  end.
  destruct (os_int_exit_masked_no_schedule_frame_post sg state _ heap Hbranch (Horder heap Hpre))
    as [exit_heap [Hsource Hpost]].
  match type of Hpost with ?P exit_heap =>
    assert (Hafter : P |-- UCOS2_inv sg returned ** armv7a_dormant_continuation abi saved **
      armv7a_task_call_stacks abi returned.(TskState) focus
        (task_stack_take returned.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame))
  end.
  { unfold returned, os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
  exists exit_heap; split; [exact Hsource|].
  exact (armv7a_irq_wrapper_restore_preserves_pending_call external platform port abi sg returned
    saved call node handler focus frame exit_heap Hbinding Hslice Hcall Hcurrent Hnode Hsp
    Hparked Haddress Hcoverage (Hafter exit_heap Hpost)).
Qed.

(** A complete source segment: the actual IRQ save event, counter/SP
    stores, OSIntExit's no-schedule branch and the matching frame restore.
    This is a branch theorem, not a restriction excluding other handlers
    or scheduling paths from the public API contract. *)
Lemma armv7a_irq_source_no_schedule_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication focus payload (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  let restored := os_int_exit_wrapper_restored_state
    (os_int_exit_counter_state parked.(SchedState).(isRunning) parked)
    saved.(armv7a_continuation_stack) in
  armv7a_task_frame_slice saved ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
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
  interrupt_exit_requests_schedule parked.(SchedState).(isRunning) parked.(IntrState) = false ->
  (os_int_exit_frame_save_pre external platform handler **
    (UCOS2_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists registry_heap exit_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap registry_heap /\
    os_int_exit_masked_no_schedule_fragment sg registry_heap exit_heap /\
    armv7a_irq_restore_pointer_reads sg exit_heap
      (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp) /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key saved.(armv7a_continuation_stack))) /\
    restored.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload /\
    (forall final, armv7a_restore_transition abi handler saved exit_heap final ->
      final.(ConAssertion.s_mem) = exit_heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved call)
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg restored ** armv7a_task_call_stacks abi restored.(TskState) focus
          restored.(TskState).(parkedTaskStacks) ** frame)) final).
Proof.
  intros external platform port abi sg entry node handler saved publication focus payload frame
    before saved_heap call parked restored Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Hfocus Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hbranch Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding Hobserved]]].
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  destruct (armv7a_irq_source_save_preserves_pending_call external platform port abi sg entry node
    handler saved publication focus payload frame before saved_heap Hslice Hrunning Hnesting
    Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hpre Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered [Hretained [Hjoint Hviews]]]]]].
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node saved.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hselected : parked.(TskState).(inUsedTaskStates)
      saved.(armv7a_continuation_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node saved.(armv7a_continuation_sp))).
  { rewrite <- Hstack, Htasks.
    cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hparked : parked.(TskState).(parkedTaskStacks)
      (task_stack_key saved.(armv7a_continuation_stack)) =
    Some (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { rewrite <- Hstack, Htasks; apply task_stack_park_fragments_lookup. }
  assert (Hcurrent_parked : parked.(SchedState).(curTaskID) =
    Some saved.(armv7a_continuation_stack).(stackLeaseSlot)).
  { rewrite <- Hstack; unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; exact Hcurrent. }
  assert (Haddress_saved : tcb_field_address
      (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)).
  { rewrite <- Hstack; exact Haddress. }
  destruct (armv7a_irq_no_schedule_restore_preserves_pending_call external platform port abi sg parked
    saved call (task_set_saved_sp node saved.(armv7a_continuation_sp)) handler focus frame registry_heap
    Hbranch Hbinding Hslice Hcall Hcurrent_parked Hselected eq_refl Hparked Haddress_saved Hcovered Hjoint)
    as [exit_heap [Hexit [Hpointers [Hrestore_coverage Hresume]]]].
  assert (Hfocus_after : restored.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { unfold restored, os_int_exit_wrapper_restored_state, os_int_exit_counter_state.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks replace_IntrS].
    rewrite task_stack_take_lookup_other; [exact Hretained|].
    rewrite <- Hstack; intro Heq; unfold call in Hnone; rewrite <- Heq in Hnone; congruence. }
  exists registry_heap, exit_heap.
  split; [exact Hwrites|]. split; [exact Hstores|]. split; [exact Hexit|].
  split; [exact Hpointers|]. split; [exact Hrestore_coverage|].
  split; [exact Hfocus_after|exact Hresume].
Qed.
