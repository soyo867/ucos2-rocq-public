Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Ordinary wrapper path, distinct from OSIntCtxSw's cache stores:
    actual current/SP reads -> single linear take -> actual frame restore
    -> BX at the saved PC/LR. All four stages meet on the SAME heap.
    This consumes the handler world; it does not invent that world or the
    original physical call/handler-stack resources. *)
Lemma mutex_del_restore_wrapper_suffix : forall external platform port critical arch
  (continuations : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg handler original state incoming fragments node bx_pc return_pc (frame : Assertion) heap,
  let focus := armv7a_call_focus original bx_pc return_pc in
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)) heap ->
  armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) /\
  exists saved,
    saved.(armv7a_continuation_call) = Some original /\
    saved.(armv7a_continuation_pc) = bx_pc /\
    saved.(armv7a_continuation_lr) = return_pc /\
    (forall restored cursor written final_cursor after,
      saved.(armv7a_continuation_sp) = node.(tcbStkPtr) ->
      armv7a_continuation_restore_reads saved heap ->
      armv7a_restore_transition continuations handler saved heap restored ->
      cursor.(kernel_restore_lr) = saved.(armv7a_continuation_lr) ->
      cursor.(kernel_restore_msr_word) = Some written ->
      armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask written ->
      armv7a_restore_suffix_transition restore cursor restored final_cursor after ->
      final_cursor.(kernel_restore_return_word) = Some return_pc /\
      after.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
      (kernel_program_closed platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) (armv7a_irq_fiq_mask written)
         (os_int_exit_wrapper_restored_state state incoming) **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       armv7a_parked_continuations continuations focus (os_int_exit_wrapper_restored_state state incoming) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame) after).
Proof.
  intros external platform port critical arch continuations restore sg handler original state incoming
    fragments node bx_pc return_pc frame heap focus Hcurrent Hnode Hparked Hkey Haddress Hpre.
  assert (Hsplit : armv7a_continuation_world continuations focus (kernel_program_inv sg) state **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame) |--
    armv7a_continuation_world continuations focus (UCOS2_inv sg) state **
      (unmap_table_rep sg **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** frame))).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  destruct (armv7a_wrapper_take_continuation external platform port continuations focus sg state incoming
    fragments node _ heap Hcurrent Hnode Hparked Hkey Haddress (Hsplit heap Hpre))
    as [Hpointers [saved [Hbinding [Hfocused [Hstack [Hfragments Howned]]]]]].
  destruct Hfocused as [Hcall [Hpc Hlr]].
  split; [exact Hpointers|]. exists saved; split; [exact Hcall|].
  split; [exact Hpc|]. split; [exact Hlr|].
  intros restored cursor written final_cursor after Hsp Hreads Hrestore Hcursor_lr Hword Hmask Hsuffix.
  assert (Hreorder : armv7a_continuation_world continuations focus (UCOS2_inv sg)
      (os_int_exit_wrapper_restored_state state incoming) **
    task_stack_fragments_rep incoming.(stackLeaseRegion) fragments **
    armv7a_dormant_continuation continuations saved **
    (unmap_table_rep sg **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (armv7a_continuation_world continuations focus (kernel_program_inv sg)
       (os_int_exit_wrapper_restored_state state incoming) ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap, Hstack, Hfragments; entailer!. }
  destruct (armv7a_restore_call_resources external platform port continuations handler saved original _
    heap restored Hcall Hreads (Hreorder heap Howned) Hrestore) as [Hmemory Hresumed].
  rewrite Hmask in Hresumed.
  assert (Hassociate : kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call saved original) (armv7a_irq_fiq_mask written) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (armv7a_continuation_world continuations focus (kernel_program_inv sg)
       (os_int_exit_wrapper_restored_state state incoming) ** frame) |--
    kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call saved original) (armv7a_irq_fiq_mask written) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     (armv7a_continuation_world continuations focus (kernel_program_inv sg)
        (os_int_exit_wrapper_restored_state state incoming) ** frame))) by entailer!.
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore
    (armv7a_continuation_resumed_call saved original) written cursor restored final_cursor after
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     (armv7a_continuation_world continuations focus (kernel_program_inv sg)
        (os_int_exit_wrapper_restored_state state incoming) ** frame)) Hword
    (Hassociate restored Hresumed) Hsuffix)
    as [Hfinal [Hmemory_final Hpost]].
  split.
  - rewrite Hfinal; cbn [kernel_restore_branch_lr kernel_restore_return_word].
    rewrite Hcursor_lr, Hlr; reflexivity.
  - split; [congruence|].
    assert (Hclose : kernel_call_execution_owned external platform
        (armv7a_continuation_resumed_call saved original) (armv7a_irq_fiq_mask written) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (armv7a_continuation_world continuations focus (kernel_program_inv sg)
          (os_int_exit_wrapper_restored_state state incoming) ** frame)) |--
      kernel_program_closed platform critical sg original.(os_sched_call_invocation)
        original.(os_sched_call_origin) (armv7a_irq_fiq_mask written)
        (os_int_exit_wrapper_restored_state state incoming) **
      os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
      armv7a_parked_continuations continuations focus (os_int_exit_wrapper_restored_state state incoming) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame).
    { unfold kernel_call_execution_owned, armv7a_continuation_world.
      rewrite kernel_program_closed_equiv.
      cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
    exact (Hclose after Hpost).
Qed.

Lemma mutex_del_restore_counter_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) before observed after,
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
     (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port continuations focus sg state frame before observed after Hpre Hsource.
  assert (Hsplit : armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame |--
    UCOS2_inv sg state **
      (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap; unfold armv7a_continuation_world; entailer!. }
  destruct (Hsplit before Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw) as [middle [Hcounter Hraw_after]].
  destruct (os_int_exit_masked_counter_fragment_frame sg owned _ middle rest before Hcounter Hjoin)
    as [produced [Hwhole Hjoined]].
  assert (produced = after) by (eapply os_int_exit_masked_counter_final_eq; eassumption).
  subst produced.
  assert (Hafter : (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
    (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame)) after).
  { exists middle, rest; split; [exact Hjoined|]. split; [split; assumption|exact Hrest]. }
  assert (Hmerge : UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (unmap_table_rep sg ** armv7a_parked_continuations continuations focus state ** frame) |--
    armv7a_continuation_world continuations focus (kernel_program_inv sg)
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { rewrite kernel_program_continuation_world_split_unmap.
    unfold armv7a_continuation_world, armv7a_parked_continuations, os_int_exit_counter_state.
    cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hafter).
Qed.

(** No hypothetical branch result is supplied. The actual counter and
    selector executions determine the new heap. Nonempty ready storage is
    a separate kernel-source safety obligation, never a BSP ABI field. *)
Lemma mutex_del_restore_same_priority_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) before after,
  state.(SchedState).(readyList) <> [] ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) before ->
  os_int_exit_masked_same_priority_fragment sg before after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
     (os_int_exit_selection_state (os_int_exit_counter_state state.(SchedState).(isRunning) state)) ** frame) after.
Proof.
  intros external platform port continuations focus sg state frame before after Hready Hpre Hsource.
  destruct Hsource as [before counted after priority Hcounter Hnest Hlock Hselect Hhigh Hcur].
  pose proof (mutex_del_restore_counter_preserves_world external platform port continuations focus sg state
    frame before true counted Hpre Hcounter) as Hcounted.
  set (counted_state := os_int_exit_counter_state state.(SchedState).(isRunning) state) in *.
  assert (Hsplit : armv7a_continuation_world continuations focus (kernel_program_inv sg) counted_state ** frame |--
    UCOS2_inv sg counted_state ** unmap_table_rep sg **
      (armv7a_parked_continuations continuations focus counted_state ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap; unfold armv7a_continuation_world; entailer!. }
  pose proof (Hsplit counted Hcounted) as Hcells.
  assert (Hvalid : UCOS2_state_inv sg counted_state).
  { destruct Hcells as [owned [rest [Hj [[kernel [table [Hj2 [[Hv Hraw] Htable]]]] Hframe]]]]. exact Hv. }
  assert (Hsg : valid_stable_glob_vars sg) by (exact (proj1 (proj1 Hvalid))).
  assert (Hregistered : task_current_prio_registered counted_state.(TskState)).
  { destruct Hvalid as [_ [Ht _]]; unfold task_in_range in Ht; tauto. }
  assert (Herase : UCOS2_inv sg counted_state ** unmap_table_rep sg **
      (armv7a_parked_continuations continuations focus counted_state ** frame) |--
    UCOS2_raw_rep sg counted_state ** unmap_table_rep sg **
      (armv7a_parked_continuations continuations focus counted_state ** frame)) by (unfold UCOS2_inv; entailer!).
  destruct (os_int_exit_selection_raw_frame_post sg counted_state _ counted Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hready (Herase counted Hcells))
    as [produced [Hselection [Hhigh' [Hcurrent Hraw_after]]]].
  assert (produced = after) by (eapply os_int_exit_selection_heap_fragment_deterministic; eassumption).
  subst produced.
  pose proof (os_int_exit_selection_state_preserves_validity sg counted_state Hvalid) as Hvalid_after.
  assert (Hmerge : UCOS2_raw_rep sg (os_int_exit_selection_state counted_state) ** unmap_table_rep sg **
      (armv7a_parked_continuations continuations focus counted_state ** frame) |--
    armv7a_continuation_world continuations focus (kernel_program_inv sg)
      (os_int_exit_selection_state counted_state) ** frame).
  { rewrite kernel_program_continuation_world_split_unmap.
    unfold armv7a_continuation_world, UCOS2_inv.
    assert (Hparked : armv7a_parked_continuations continuations focus (os_int_exit_selection_state counted_state) =
      armv7a_parked_continuations continuations focus counted_state) by reflexivity.
    rewrite Hparked; entailer!. }
  exact (Hmerge after Hraw_after).
Qed.

Inductive MutexDelRestoreExitKind : Type :=
| MutexDelRestoreNoSchedule
| MutexDelRestoreSamePriority.

Definition mutex_del_restore_exit_execution (sg : StableGlobVars) (kind : MutexDelRestoreExitKind)
  (before after : model) : Prop :=
  match kind with
  | MutexDelRestoreNoSchedule => os_int_exit_masked_no_schedule_fragment sg before after
  | MutexDelRestoreSamePriority => os_int_exit_masked_same_priority_fragment sg before after
  end.

Definition mutex_del_restore_exit_state (kind : MutexDelRestoreExitKind) (state : UCOS2_Verify_State) :=
  let counted := os_int_exit_counter_state state.(SchedState).(isRunning) state in
  match kind with
  | MutexDelRestoreNoSchedule => counted
  | MutexDelRestoreSamePriority => os_int_exit_selection_state counted
  end.

Lemma mutex_del_restore_exit_preserves_world : forall external platform port
  (continuations : Armv7aContinuationABI external platform port) focus sg kind state
  (frame : Assertion) before after,
  (kind = MutexDelRestoreSamePriority -> state.(SchedState).(readyList) <> []) ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg) state ** frame) before ->
  mutex_del_restore_exit_execution sg kind before after ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
     (mutex_del_restore_exit_state kind state) ** frame) after.
Proof.
  intros external platform port continuations focus sg kind state frame before after Hready Hpre Hsource.
  destruct kind; cbn [mutex_del_restore_exit_execution mutex_del_restore_exit_state] in *.
  - eapply restore_handler_no_schedule_preserves_world; eassumption.
  - eapply mutex_del_restore_same_priority_preserves_world; [apply Hready; reflexivity|exact Hpre|exact Hsource].
Qed.

Definition mutex_del_restore_handler_owner (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (handler : OsIntExitCallContext) : Assertion :=
  interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
  os_int_exit_context_resources port handler.

(** These facts come from the actual entry SP store and park operation.
    They are not BSP outputs and do not require the interrupted task to be
    ready. Later registered counter bodies preserve precisely these two
    projections; a future task-changing registry must prove its own join. *)
Lemma mutex_del_restore_parked_wrapper_binding : forall entry call sp fragments node,
  entry.(SchedState).(isRunning) = true ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  let parked := armv7a_irq_live_parked_state entry call sp fragments in
  parked.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
  parked.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node sp) /\
  parked.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments).
Proof.
  intros entry call sp fragments node Hrunning Hcurrent Hnode parked.
  unfold parked, armv7a_irq_live_parked_state; cbn [replace_TskS SchedState TskState
    glob_task_set_parked_stacks inUsedTaskStates parkedTaskStacks].
  split.
  - unfold armv7a_irq_live_entry_state, os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    rewrite Hrunning; exact Hcurrent.
  - split.
    + unfold armv7a_irq_live_entry_state; apply os_sched_save_current_sp_live_value.
      unfold armv7a_irq_entry_counter_state; rewrite Hrunning; exact Hnode.
    + apply task_stack_park_fragments_lookup.
Qed.

(** Conditional source-cut consumer for a public Restore's ordinary
    interrupted branch. The front MSR, exception save, entry counter/SP
    writes, actual BSP return, wrapper-private join, either nonswitching OSIntExit body, current
    and SP reads, capsule take, exception restore and final BX are composed
    on the exact successive models. The BSP is not treated as a no-op.

    This is deliberately NOT the public C Require/Ensure: its physical
    caller context and inactive handler stack are real input owners. The
    original Del declaration does not yet supply them. The registry is
    the checked counter-body subset, not arbitrary ISR or switched tasks.
    The final continuation consumes actual restore/BX transitions; neither
    their existence nor eventual scheduling is asserted. *)
Lemma mutex_del_restore_ordinary_continuation : forall external platform port critical arch
  (continuations : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg handler cpu_word entry checkpoint node deposited publication cursor before written_cursor released
  saved_heap handler_heap Local local_step normal_return
  (bsp : RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    local_step normal_return)
  handler_cursor returned_cursor returned_heap exit_cursor exit_heap exit_kind exited_heap (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc) cursor.(kernel_restore_lr) in
  let parked := armv7a_irq_live_parked_state checkpoint call deposited.(armv7a_continuation_sp)
    deposited.(armv7a_continuation_fragments) in
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
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    deposited.(armv7a_continuation_sp) ->
  deposited.(armv7a_continuation_lr) = cursor.(kernel_restore_lr) ->
  cursor.(kernel_restore_r0) = cpu_word ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (exit_kind = MutexDelRestoreSamePriority -> checkpoint.(SchedState).(readyList) <> []) ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) cpu_word entry **
   os_sched_context_resources external call **
   (kernel_program_inv sg checkpoint **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  armv7a_save_transition continuations handler deposited released saved_heap ->
  kernel_heap_execution
    (armv7a_irq_live_entry_writes sg checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
      deposited.(armv7a_continuation_sp)) saved_heap handler_heap ->
  normal_return sg handler_cursor handler_heap returned_cursor returned_heap ->
  local_step returned_cursor returned_heap exit_cursor exit_heap ->
  mutex_del_restore_exit_execution sg exit_kind exit_heap exited_heap ->
  exists body_state saved,
    body_state.(TskState) = parked.(TskState) /\ body_state.(SchedState) = parked.(SchedState) /\
    restore_handler_execution local_step sg handler_cursor handler_heap returned_cursor returned_heap /\
    returned_cursor.(restore_handler_current_call) = handler_cursor.(restore_handler_current_call) /\
    returned_cursor.(restore_handler_pc) =
      handler_cursor.(restore_handler_current_call).(restore_handler_return_word) /\
    armv7a_irq_restore_pointer_reads sg exited_heap
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) deposited.(armv7a_continuation_sp) /\
    saved.(armv7a_continuation_call) = Some call /\
    saved.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    saved.(armv7a_continuation_lr) = cursor.(kernel_restore_lr) /\
    (forall restored final_cursor after,
      saved.(armv7a_continuation_sp) = deposited.(armv7a_continuation_sp) ->
      armv7a_continuation_restore_reads saved exited_heap ->
      armv7a_restore_transition continuations handler saved exited_heap restored ->
      armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask cpu_word ->
      armv7a_restore_suffix_transition restore written_cursor restored final_cursor after ->
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (kernel_program_closed platform critical sg call.(os_sched_call_invocation)
         call.(os_sched_call_origin) (armv7a_irq_fiq_mask cpu_word)
         (os_int_exit_wrapper_restored_state
           (mutex_del_restore_exit_state exit_kind body_state) call.(os_sched_call_stack)) **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved call) **
       armv7a_parked_continuations continuations focus
         (os_int_exit_wrapper_restored_state
           (mutex_del_restore_exit_state exit_kind body_state) call.(os_sched_call_stack)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       frame) after).
Proof.
  intros external platform port critical arch continuations restore sg handler cpu_word entry checkpoint
    node deposited publication cursor before written_cursor released saved_heap handler_heap Local local_step
    normal_return bsp handler_cursor returned_cursor returned_heap exit_cursor exit_heap exit_kind exited_heap frame
    call focus parked Hhandler_mask Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion
    Hgeometry Hpublication Hsp Hlr Hr0 Hmask Hready Hpre Hprefix Hsave Hentry Hreturn Hwrapper Hexit.
  destruct (kernel_program_restore_prefix_irq_input external platform port critical arch continuations restore
    sg handler cpu_word entry checkpoint cursor before written_cursor released frame
    Hhandler_mask Hnone Hr0 Hmask Hpre Hprefix) as [Hwritten [Hprefix_mem Hirq]].
  assert (Hdeposit_pre : (os_int_exit_frame_save_pre external platform handler **
    (armv7a_continuation_world continuations
      (armv7a_call_focus call handler.(os_int_exit_interrupted_pc) deposited.(armv7a_continuation_lr))
      (kernel_program_inv sg) checkpoint ** frame)) released).
  { rewrite Hlr; exact Hirq. }
  destruct (kernel_program_irq_source_save_deposit external platform port continuations sg checkpoint node
    handler deposited publication frame released saved_heap Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hdeposit_pre Hsave)
    as [produced [Hcall [Hpc [Hsave_writes [Hentry_run Hhandler]]]]].
  assert (produced = handler_heap) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; rewrite Hlr in Hhandler.
  assert (Hhandler_pre : (armv7a_continuation_world continuations focus (kernel_program_inv sg) parked **
    (mutex_del_restore_handler_owner platform port handler ** frame)) handler_heap).
  { assert (Horder : armv7a_continuation_world continuations focus (kernel_program_inv sg) parked **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame) |--
      armv7a_continuation_world continuations focus (kernel_program_inv sg) parked **
        (mutex_del_restore_handler_owner platform port handler ** frame)).
    { unfold mutex_del_restore_handler_owner; entailer!. }
    exact (Horder handler_heap Hhandler). }
  destruct (restore_handler_normal_return_preserves_world external platform port continuations focus Local
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    local_step normal_return bsp sg parked handler_cursor handler_heap returned_cursor returned_heap frame
    Hreturn Hhandler_pre) as [body_state [Htrace [Hsame [Hreturn_pc [Ht [Hs Hbody]]]]]].
  assert (Hprivate_first : armv7a_continuation_world continuations focus (kernel_program_inv sg) body_state **
      (mutex_del_restore_handler_owner platform port handler ** frame) |--
    mutex_del_restore_handler_owner platform port handler **
      (armv7a_continuation_world continuations focus (kernel_program_inv sg) body_state ** frame)) by entailer!.
  pose proof (restore_handler_local_resources _ _ _ bsp returned_cursor returned_heap exit_cursor exit_heap _
    Hwrapper (Hprivate_first returned_heap Hbody)) as Hmasked_handler.
  assert (Hworld_first : mutex_del_restore_handler_owner platform port handler **
      (armv7a_continuation_world continuations focus (kernel_program_inv sg) body_state ** frame) |--
    armv7a_continuation_world continuations focus (kernel_program_inv sg) body_state **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)).
  { unfold mutex_del_restore_handler_owner; entailer!. }
  assert (Hbody_ready : exit_kind = MutexDelRestoreSamePriority -> body_state.(SchedState).(readyList) <> []).
  { intros Hkind; rewrite Hs; unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    rewrite Hrunning; exact (Hready Hkind). }
  pose proof (mutex_del_restore_exit_preserves_world external platform port continuations focus sg exit_kind
    body_state _ exit_heap exited_heap Hbody_ready (Hworld_first exit_heap Hmasked_handler) Hexit) as Hexit_world.
  set (exited := mutex_del_restore_exit_state exit_kind body_state) in *.
  destruct (mutex_del_restore_parked_wrapper_binding checkpoint call deposited.(armv7a_continuation_sp)
    deposited.(armv7a_continuation_fragments) node Hrunning Hcurrent Hnode)
    as [Hpark_current [Hpark_node Hparked]].
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
  destruct (mutex_del_restore_wrapper_suffix external platform port critical arch continuations restore sg handler
    call exited call.(os_sched_call_stack) deposited.(armv7a_continuation_fragments)
    (task_set_saved_sp node deposited.(armv7a_continuation_sp)) handler.(os_int_exit_interrupted_pc)
    cursor.(kernel_restore_lr) frame exited_heap Hexit_current Hexit_node Hexit_parked eq_refl Haddress Hexit_world)
    as [Hpointers [saved [Hsaved_call [Hsaved_pc [Hsaved_lr Hconsume]]]]].
  exists body_state, saved; split; [exact Ht|]. split; [exact Hs|]. split; [exact Htrace|].
  split; [exact Hsame|]. split; [exact Hreturn_pc|]. split; [exact Hpointers|].
  split; [exact Hsaved_call|]. split; [exact Hsaved_pc|]. split; [exact Hsaved_lr|].
  intros restored final_cursor after Hsaved_sp Hreads Hrestore Hsaved_mask Hsuffix.
  set (written := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hwritten_mask : armv7a_irq_fiq_mask written = armv7a_irq_fiq_mask cpu_word).
  { unfold written; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity. }
  assert (Hcursor_lr : written_cursor.(kernel_restore_lr) = saved.(armv7a_continuation_lr)).
  { rewrite Hwritten; cbn [kernel_restore_write_cpsr kernel_restore_lr]; symmetry; exact Hsaved_lr. }
  assert (Hword : written_cursor.(kernel_restore_msr_word) = Some written).
  { rewrite Hwritten; reflexivity. }
  assert (Hsaved_written : armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask written)
    by congruence.
  destruct (Hconsume restored written_cursor written final_cursor after Hsaved_sp Hreads Hrestore
    Hcursor_lr Hword Hsaved_written Hsuffix) as [Hfinal [Hmemory Hpost]].
  split; [exact Hfinal|]. rewrite Hwritten_mask in Hpost; exact Hpost.
Qed.
