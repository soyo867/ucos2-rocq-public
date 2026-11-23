Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One entry of the EXISTING parked map, with the already defined pending
    call/PC/LR observation retained at its key. Other entries keep their
    whole strong owner, including initial-entry frames. This is not a
    second map or token: the distinguished entry owns exactly one dormant
    continuation, and every byte remains in store_parked_stacks. *)
Definition armv7a_task_call_stack_entry {external platform port}
  (abi : Armv7aContinuationABI external platform port) (tasks : Glob_TaskAbstractState)
  (focus : Armv7aCallFocus) (key : TaskID * nat)
  (payload : TaskStackRegion * TaskStackFragments) : Assertion :=
  if task_stack_key_eq_dec key (armv7a_call_focus_key focus) then
    EX saved,
      coq_prop (armv7a_continuation_binding saved /\
        armv7a_continuation_focus_binding focus saved /\
        task_stack_key saved.(armv7a_continuation_stack) = key /\
        (saved.(armv7a_continuation_stack).(stackLeaseRegion),
          saved.(armv7a_continuation_fragments)) = payload /\
        armv7a_task_frame_slice saved /\
        task_stack_live_sp tasks key saved.(armv7a_continuation_sp)) &&
      armv7a_dormant_continuation abi saved
  else armv7a_task_stack_entry abi tasks key payload.

Definition armv7a_task_call_stacks {external platform port}
  (abi : Armv7aContinuationABI external platform port) tasks focus stacks : Assertion :=
  store_parked_continuations (armv7a_task_call_stack_entry abi tasks focus) stacks.

Lemma armv7a_task_call_stack_entry_forget : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus key payload,
  armv7a_task_call_stack_entry abi tasks focus key payload |--
  armv7a_task_stack_entry abi tasks key payload.
Proof.
  intros; unfold armv7a_task_call_stack_entry.
  destruct task_stack_key_eq_dec; [|reflexivity].
  Intros saved; unfold armv7a_task_stack_entry; Exists saved.
  assert (Hcall : saved.(armv7a_continuation_call) = Some focus.(armv7a_focus_call))
    by (unfold armv7a_continuation_focus_binding in *; tauto).
  unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!.
Qed.

Lemma armv7a_task_call_stacks_forget : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus stacks,
  armv7a_task_call_stacks abi tasks focus stacks |--
  armv7a_task_stack_continuations abi tasks stacks.
Proof.
  intros; unfold armv7a_task_call_stacks, armv7a_task_stack_continuations, store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros; apply armv7a_task_call_stack_entry_forget.
Qed.

(** A new pending call can be focused only while its key is absent. An
    arbitrary existing stack entry cannot be relabelled as that call. *)
Lemma armv7a_task_call_stacks_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus stacks,
  stacks (armv7a_call_focus_key focus) = None ->
  armv7a_task_stack_continuations abi tasks stacks |--
  armv7a_task_call_stacks abi tasks focus stacks.
Proof.
  intros external platform port abi tasks focus stacks Hnone.
  unfold armv7a_task_call_stacks, armv7a_task_stack_continuations, store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros key payload Hlookup.
  unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec as [Heq|Hne].
  - subst key; rewrite Hnone in Hlookup; discriminate.
  - reflexivity.
Qed.

Lemma armv7a_task_call_stacks_park : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus stacks saved,
  armv7a_continuation_binding saved -> armv7a_continuation_focus_binding focus saved ->
  task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus ->
  armv7a_task_frame_slice saved ->
  task_stack_live_sp tasks (task_stack_key saved.(armv7a_continuation_stack))
    saved.(armv7a_continuation_sp) ->
  stacks (task_stack_key saved.(armv7a_continuation_stack)) = None ->
  armv7a_dormant_continuation abi saved ** armv7a_task_stack_continuations abi tasks stacks |--
  armv7a_task_call_stacks abi tasks focus
    (task_stack_park_fragments stacks saved.(armv7a_continuation_stack)
      saved.(armv7a_continuation_fragments)).
Proof.
  intros external platform port abi tasks focus stacks saved Hbinding Hfocus Hkey Hslice Hsp Hnone.
  assert (Habsent : stacks (armv7a_call_focus_key focus) = None) by congruence.
  sep_apply_l_atomic (armv7a_task_call_stacks_absent external platform port abi tasks focus stacks Habsent).
  assert (Hentry : armv7a_dormant_continuation abi saved |--
    armv7a_task_call_stack_entry abi tasks focus (task_stack_key saved.(armv7a_continuation_stack))
      (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec; [|contradiction].
    Exists saved; entailer!. }
  sep_apply_l_atomic Hentry; unfold armv7a_task_call_stacks.
  apply store_parked_continuations_park; exact Hnone.
Qed.

(** Take both the concrete bytes and the one dormant owner. The result
    identifies the pending call, PC and LR from the stored entry itself;
    the remaining map keeps all strong facts for the other tasks. *)
Lemma armv7a_task_call_stacks_take : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus stacks lease fragments,
  stacks (task_stack_key lease) = Some (lease.(stackLeaseRegion), fragments) ->
  task_stack_key lease = armv7a_call_focus_key focus ->
  store_parked_stacks stacks ** armv7a_task_call_stacks abi tasks focus stacks |--
  EX saved,
    coq_prop (armv7a_continuation_binding saved /\
      armv7a_continuation_focus_binding focus saved /\
      saved.(armv7a_continuation_stack) = lease /\
      saved.(armv7a_continuation_fragments) = fragments /\
      armv7a_task_frame_slice saved /\
      task_stack_live_sp tasks (task_stack_key lease) saved.(armv7a_continuation_sp)) &&
    (task_stack_fragments_rep lease.(stackLeaseRegion) fragments **
     armv7a_dormant_continuation abi saved **
     store_parked_stacks (task_stack_take stacks lease) **
     armv7a_task_stack_continuations abi tasks (task_stack_take stacks lease)).
Proof.
  intros external platform port abi tasks focus stacks lease fragments Hlookup Hfocus.
  sep_apply_l_atomic (store_parked_stacks_take_fragments stacks lease fragments Hlookup).
  unfold armv7a_task_call_stacks.
  sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_call_stack_entry abi tasks focus)
    stacks lease fragments Hlookup).
  fold (armv7a_task_call_stacks abi tasks focus (task_stack_take stacks lease)).
  sep_apply_l_atomic (armv7a_task_call_stacks_forget external platform port abi tasks focus
    (task_stack_take stacks lease)).
  unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec; [|contradiction].
  Intros saved.
  assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = task_stack_key lease) by tauto.
  assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
    saved.(armv7a_continuation_fragments)) = (lease.(stackLeaseRegion), fragments)) by tauto.
  assert (Hlease : saved.(armv7a_continuation_stack) = lease).
  { unfold task_stack_key in Hkey; destruct saved.(armv7a_continuation_stack), lease;
      cbn in *; congruence. }
  Exists saved; entailer!; congruence.
Qed.

(** Real wrapper reads followed by a linear take. Only the selected key
    is supplied by control flow; the selected invocation and saved PC/LR
    are recovered from the entry deposited earlier, not assumed here. *)
Lemma armv7a_irq_wrapper_take_call_stack : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state focus incoming fragments
  node (frame : Assertion) heap,
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let restored := os_int_exit_wrapper_restored_state state incoming in
  exists saved,
    armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads saved heap /\
    armv7a_continuation_focus_binding focus saved /\
    saved.(armv7a_continuation_stack) = incoming /\
    saved.(armv7a_continuation_fragments) = fragments /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
    (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
      restored.(TskState) restored.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     armv7a_dormant_continuation abi saved ** frame) heap.
Proof.
  intros external platform port abi sg state focus incoming fragments node frame heap
    Hcurrent Hnode Hgen Hparked Hfocus Haddress Hcoverage Hpre restored.
  assert (Horder : UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) ** frame |--
    UCOS2_inv sg state ** (armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) ** frame)) by entailer!.
  assert (Hpointers : armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr)).
  { destruct (Horder heap Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_live; eassumption. }
  assert (Htake : UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) ** frame |--
    EX saved,
      coq_prop (armv7a_continuation_binding saved /\
        armv7a_continuation_focus_binding focus saved /\
        saved.(armv7a_continuation_stack) = incoming /\
        saved.(armv7a_continuation_fragments) = fragments /\
        armv7a_task_frame_slice saved /\
        task_stack_live_sp state.(TskState) (task_stack_key incoming) saved.(armv7a_continuation_sp)) &&
      (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
        restored.(TskState) restored.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
         saved.(armv7a_continuation_fragments) **
       armv7a_dormant_continuation abi saved ** frame)).
  { rewrite UCOS2_inv_split_parked_stacks; Intros.
    assert (Hvalid : UCOS2_state_inv sg state) by assumption.
    assert (Hconsistent : parked_stacks_consistent state.(TskState)
      (task_stack_take state.(TskState).(parkedTaskStacks) incoming)).
    { apply task_stack_take_preserves_consistency.
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
    sep_apply_l_atomic (armv7a_task_call_stacks_take external platform port abi state.(TskState)
      focus state.(TskState).(parkedTaskStacks) incoming fragments Hparked Hfocus).
    Intros saved.
    sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg state _ Hvalid Hconsistent).
    assert (Hlease : saved.(armv7a_continuation_stack) = incoming) by tauto.
    assert (Hfragments : saved.(armv7a_continuation_fragments) = fragments) by tauto.
    Exists saved; rewrite Hlease, Hfragments.
    unfold restored, os_int_exit_wrapper_restored_state;
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks]; entailer!. }
  destruct (Htake heap Hpre) as [saved [[Hbinding [Hfocused [Hlease [Hfragments [Hslice Hsp]]]]] Hresources]].
  assert (Hnode_sp : node.(tcbStkPtr) = saved.(armv7a_continuation_sp)).
  { apply Hsp; assumption. }
  assert (Hreads : armv7a_continuation_restore_reads saved heap).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    assert (Hframe : UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
        restored.(TskState) restored.(TskState).(parkedTaskStacks) **
        task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
          saved.(armv7a_continuation_fragments) **
        armv7a_dormant_continuation abi saved ** frame |--
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
        restored.(TskState) restored.(TskState).(parkedTaskStacks) **
       armv7a_dormant_continuation abi saved ** frame)) by entailer!.
    exact (Hframe heap Hresources). }
  exists saved; rewrite Hnode_sp in Hpointers.
  split; [exact Hpointers|]. split; [exact Hreads|]. split; [exact Hfocused|].
  split; [exact Hlease|]. split; [exact Hfragments|].
  split; [apply task_stack_take_covers_selected; exact Hcoverage|exact Hresources].
Qed.

(** The handler actually exchanges its CPU token for the saved call's
    execution. The descriptor comes from the map-owned take above; no
    saved-call equality or separate restore-read premise is supplied by
    this consumer. The same remaining strong map and private frame return. *)
Lemma armv7a_irq_wrapper_resume_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state focus incoming fragments
  node handler (frame : Assertion) heap,
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  let restored := os_int_exit_wrapper_restored_state state incoming in
  exists saved,
    armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus saved /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
    (forall final, armv7a_restore_transition abi handler saved heap final ->
      final.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
         restored.(TskState) restored.(TskState).(parkedTaskStacks) ** frame)) final).
Proof.
  intros external platform port abi sg state focus incoming fragments node handler frame heap
    Hcurrent Hnode Hgen Hparked Hfocus Haddress Hcoverage Hpre restored.
  destruct (armv7a_irq_wrapper_take_call_stack external platform port abi sg state focus incoming
    fragments node _ heap Hcurrent Hnode Hgen Hparked Hfocus Haddress Hcoverage Hpre)
    as [saved [Hpointers [Hreads [Hfocused [Hlease [Hfragments [Hcovered Hresources]]]]]]].
  exists saved; split; [exact Hpointers|]. split; [exact Hfocused|].
  split; [exact Hcovered|]. intros final Hrun.
  apply (armv7a_restore_call_resources external platform port abi handler saved
    focus.(armv7a_focus_call) _ heap final (proj1 Hfocused) Hreads); [|exact Hrun].
  match type of Hresources with ?P heap =>
    assert (Horder : P |--
      interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
      (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
        restored.(TskState) restored.(TskState).(parkedTaskStacks) ** frame)) by entailer!
  end.
  exact (Horder heap Hresources).
Qed.

(** The actual IRQ counter/SP producer deposits the SAME call descriptor
    beside its frame. This establishes the focus at the save boundary,
    before any selected-key consumer uses it. No current map can simply
    be assumed to have the desired focused entry. *)
Lemma armv7a_irq_live_entry_parks_call : forall external platform port
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
  let focus := armv7a_call_focus call saved.(armv7a_continuation_pc) saved.(armv7a_continuation_lr) in
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  exists final,
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
      parked.(TskState).(parkedTaskStacks) ** frame) final.
Proof.
  intros external platform port abi sg entry node saved call publication frame heap Hcall Hbinding
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication
    Hsp Hcoverage Hpre focus parked.
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
  assert (Hfocused : armv7a_continuation_focus_binding focus saved)
    by (unfold focus, armv7a_call_focus, armv7a_continuation_focus_binding; cbn; tauto).
  assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = armv7a_call_focus_key focus).
  { unfold focus, armv7a_call_focus, armv7a_call_focus_key; cbn; rewrite Hstack; reflexivity. }
  assert (Hattach : armv7a_dormant_continuation abi saved **
      armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_call_stacks abi parked.(TskState) focus parked.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic Hreindex; rewrite Hmap, Hstack.
    assert (Habsent : entry.(TskState).(parkedTaskStacks)
      (task_stack_key saved.(armv7a_continuation_stack)) = None) by (rewrite <- Hstack; exact Hnone).
    sep_apply_r_atomic (armv7a_task_call_stacks_park external platform port abi parked.(TskState)
      focus entry.(TskState).(parkedTaskStacks) saved Hbinding Hfocused Hkey Hslice Hlive Habsent).
    entailer!. }
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
    UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
      parked.(TskState).(parkedTaskStacks) ** frame).
  { assert (Horder : UCOS2_inv sg parked **
        (armv7a_dormant_continuation abi saved **
         armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) ** frame) |--
      (armv7a_dormant_continuation abi saved **
       armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks)) **
      (UCOS2_inv sg parked ** frame)) by entailer!.
    intros whole Hheap.
    destruct (Horder whole Hheap) as [caps [other [Hjoined [Hcaps Hother]]]].
    assert (Hattached : (armv7a_task_call_stacks abi parked.(TskState) focus
        parked.(TskState).(parkedTaskStacks) ** (UCOS2_inv sg parked ** frame)) whole).
    { exists caps, other; split; [exact Hjoined|]. split; [exact (Hattach caps Hcaps)|exact Hother]. }
    assert (Hfinish : armv7a_task_call_stacks abi parked.(TskState) focus
        parked.(TskState).(parkedTaskStacks) ** (UCOS2_inv sg parked ** frame) |--
      UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
        parked.(TskState).(parkedTaskStacks) ** frame) by entailer!.
    exact (Hfinish whole Hattached). }
  apply (Hmerge final); exists updated, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** Consume the real original CPU/context at the approved save transition,
    then perform the kernel counter/SP stores. The frame-slice argument is
    the mathematical image fact produced by armv7a_irq_save_fragment_execution;
    it supplies neither bytes nor CPU authority. No focused owner is an
    input. PC agreement is obtained from this same save event. *)
Lemma armv7a_irq_source_save_parks_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  armv7a_task_frame_slice saved ->
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
  (os_int_exit_frame_save_pre external platform handler **
    (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc)
    saved.(armv7a_continuation_lr) in
  exists final,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_inv sg parked ** armv7a_task_call_stacks abi parked.(TskState) focus
      parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler saved publication frame before saved_heap call
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication
    Hsp Hcoverage Hpre Hsave parked focus.
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hmask [Hpc [Hsavedsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler saved call _ before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsavedsp Hfragments Hpre Hsave) as [Hwrites Hsaved].
  match type of Hsaved with ?P saved_heap =>
    assert (Horder : P |-- UCOS2_inv sg entry **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
      armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)) by entailer!
  end.
  destruct (armv7a_irq_live_entry_parks_call external platform port abi sg entry node saved call
    publication _ saved_heap Hcall Hbinding Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Horder saved_heap Hsaved))
    as [final [Hrun [Hcovered Hpost]]].
  exists final; split; [exact Hwrites|]. split; [exact Hrun|]. split; [exact Hcovered|].
  unfold focus; rewrite <- Hpc; exact Hpost.
Qed.

(** A concrete C exit path consumes the retained call-aware map, then
    actual wrapper reads and the ABI exchange restore that pending call.
    This starts AFTER the BSP/handler body: that body must transport the
    map on its own source execution, not satisfy an assumed unchanged
    endpoint. No schedule, termination or arbitrary-ISR claim is added. *)
Lemma armv7a_irq_no_schedule_resumes_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state focus incoming fragments
  node handler (frame : Assertion) heap,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  let returned := os_int_exit_counter_state state.(SchedState).(isRunning) state in
  let restored := os_int_exit_wrapper_restored_state returned incoming in
  exists exit_heap saved,
    os_int_exit_masked_no_schedule_fragment sg heap exit_heap /\
    armv7a_irq_restore_pointer_reads sg exit_heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus saved /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
    (forall final, armv7a_restore_transition abi handler saved exit_heap final ->
      final.(ConAssertion.s_mem) = exit_heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
         restored.(TskState) restored.(TskState).(parkedTaskStacks) ** frame)) final).
Proof.
  intros external platform port abi sg state focus incoming fragments node handler frame heap
    Hbranch Hcurrent Hnode Hgen Hparked Hfocus Haddress Hcoverage Hpre returned restored.
  match type of Hpre with ?P heap =>
    assert (Horder : P |-- UCOS2_inv sg state **
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** frame))) by entailer!
  end.
  destruct (os_int_exit_masked_no_schedule_frame_post sg state _ heap Hbranch (Horder heap Hpre))
    as [exit_heap [Hrun Hpost]].
  match type of Hpost with ?P exit_heap =>
    assert (Hafter : P |-- UCOS2_inv sg returned **
      armv7a_task_call_stacks abi returned.(TskState) focus returned.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame))
  end.
  { unfold returned, os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
  destruct (armv7a_irq_wrapper_resume_call external platform port abi sg returned focus incoming
    fragments node handler frame exit_heap Hcurrent Hnode Hgen Hparked Hfocus Haddress Hcoverage
    (Hafter exit_heap Hpost)) as [saved Hsaved].
  exists exit_heap, saved; split; assumption.
Qed.

(** The other normally returning nonswitch branch performs real ready-table
    selection/high-cache writes. It retains OSUnMapTbl exactly once, not
    as a newly assumed post-call table, then restores the pending call. *)
Lemma armv7a_irq_same_priority_resumes_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state focus incoming fragments
  node handler (frame : Assertion) heap,
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = armv7a_call_focus_key focus ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** unmap_table_rep sg **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  let returned := os_int_exit_same_priority_state state in
  let restored := os_int_exit_wrapper_restored_state returned incoming in
  exists exit_heap saved,
    os_int_exit_masked_same_priority_fragment sg heap exit_heap /\
    armv7a_irq_restore_pointer_reads sg exit_heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus saved /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
    (forall final, armv7a_restore_transition abi handler saved exit_heap final ->
      final.(ConAssertion.s_mem) = exit_heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
         restored.(TskState) restored.(TskState).(parkedTaskStacks) **
        (unmap_table_rep sg ** frame))) final).
Proof.
  intros external platform port abi sg state focus incoming fragments node handler frame heap
    Hrunning Hschedule Hnonempty Hequal Hcurrent Hnode Hgen Hparked Hfocus Haddress Hcoverage
    Hpre returned restored.
  match type of Hpre with ?P heap =>
    assert (Horder : P |-- UCOS2_inv sg state ** unmap_table_rep sg **
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** frame))) by entailer!
  end.
  destruct (os_int_exit_masked_same_priority_frame_post sg state _ heap
    Hrunning Hschedule Hnonempty Hequal (Horder heap Hpre)) as [exit_heap [Hrun Hpost]].
  match type of Hpost with ?P exit_heap =>
    assert (Hafter : P |-- UCOS2_inv sg returned **
      armv7a_task_call_stacks abi returned.(TskState) focus returned.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (unmap_table_rep sg ** frame)))
  end.
  { unfold returned, os_int_exit_same_priority_state, os_int_exit_selection_state,
      os_int_exit_counter_state; cbn [replace_IntrS replace_SchedS TskState]; entailer!. }
  destruct (armv7a_irq_wrapper_resume_call external platform port abi sg returned focus incoming
    fragments node handler (unmap_table_rep sg ** frame) exit_heap Hcurrent Hnode Hgen Hparked
    Hfocus Haddress Hcoverage (Hafter exit_heap Hpost)) as [saved Hsaved].
  exists exit_heap, saved; split; assumption.
Qed.
