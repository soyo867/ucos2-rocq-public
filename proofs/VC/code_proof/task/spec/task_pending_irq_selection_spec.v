Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_irq_sched_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The scheduling-enabled IRQ exit really updates the highest-ready cache.
    Reuse that source producer and the exact-descriptor restore consumer.
    The pending caller's map and OSUnMapTbl each retain one spatial owner. *)
Lemma armv7a_irq_same_priority_restore_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg state saved call node handler focus (frame : Assertion) heap,
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
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
  (UCOS2_inv sg state ** unmap_table_rep sg ** armv7a_dormant_continuation abi saved **
   armv7a_task_call_stacks abi state.(TskState) focus
     (task_stack_take state.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  let returned := os_int_exit_same_priority_state state in
  let restored := os_int_exit_wrapper_restored_state returned saved.(armv7a_continuation_stack) in
  exists exit_heap,
    os_int_exit_masked_same_priority_fragment sg heap exit_heap /\
    armv7a_irq_restore_pointer_reads sg exit_heap
      (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp) /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key saved.(armv7a_continuation_stack))) /\
    (forall final, armv7a_restore_transition abi handler saved exit_heap final ->
      final.(ConAssertion.s_mem) = exit_heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved call)
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg restored ** armv7a_task_call_stacks abi restored.(TskState) focus
          restored.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) final).
Proof.
  intros external platform port abi sg state saved call node handler focus frame heap Hrunning Hschedule Hnonempty Hequal
    Hbinding Hslice Hcall Hcurrent Hnode Hsp Hparked Haddress Hcoverage Hpre returned restored.
  match type of Hpre with ?P heap =>
    assert (Horder : P |-- UCOS2_inv sg state ** unmap_table_rep sg **
      (armv7a_dormant_continuation abi saved **
       armv7a_task_call_stacks abi state.(TskState) focus
         (task_stack_take state.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** frame))) by entailer!
  end.
  destruct (os_int_exit_masked_same_priority_frame_post sg state _ heap Hrunning Hschedule Hnonempty Hequal (Horder heap Hpre))
    as [exit_heap [Hsource Hpost]].
  match type of Hpost with ?P exit_heap =>
    assert (Hafter : P |-- UCOS2_inv sg returned ** armv7a_dormant_continuation abi saved **
      armv7a_task_call_stacks abi returned.(TskState) focus
        (task_stack_take returned.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (unmap_table_rep sg ** frame)))
  end.
  { unfold returned, os_int_exit_same_priority_state, os_int_exit_selection_state,
      os_int_exit_counter_state; cbn [replace_IntrS replace_SchedS TskState]; entailer!. }
  exists exit_heap; split; [exact Hsource|].
  exact (armv7a_irq_wrapper_restore_preserves_pending_call external platform port abi sg returned
    saved call node handler focus (unmap_table_rep sg ** frame) exit_heap Hbinding Hslice Hcall Hcurrent Hnode Hsp
    Hparked Haddress Hcoverage (Hafter exit_heap Hpost)).
Qed.

(** The actual save and entry stores feed that selection branch on the
    same heap. The older focused key remains present after the new frame
    is taken back for return. *)
Lemma armv7a_irq_source_same_priority_preserves_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication focus payload (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  let restored := os_int_exit_wrapper_restored_state
    (os_int_exit_same_priority_state parked)
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
  interrupt_exit_requests_schedule true parked.(IntrState) = true ->
  parked.(SchedState).(readyList) <> [] ->
  sched_selected_priority parked.(TskState) parked.(SchedState) =
    sched_priority_byte parked.(SchedState).(curSchedPrio) ->
  (os_int_exit_frame_save_pre external platform handler **
    (UCOS2_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists registry_heap exit_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap registry_heap /\
    os_int_exit_masked_same_priority_fragment sg registry_heap exit_heap /\
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
          restored.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) final).
Proof.
  intros external platform port abi sg entry node handler saved publication focus payload frame
    before saved_heap call parked restored Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Hfocus Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hschedule Hnonempty Hequal Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding Hobserved]]].
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  destruct (armv7a_irq_source_save_preserves_pending_call external platform port abi sg entry node
    handler saved publication focus payload (unmap_table_rep sg ** frame) before saved_heap Hslice Hrunning Hnesting
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
  assert (Hrunning_parked : parked.(SchedState).(isRunning) = true).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; exact Hrunning. }
  match type of Hjoint with ?P registry_heap => assert (Horder : P |--
    UCOS2_inv sg parked ** unmap_table_rep sg ** armv7a_dormant_continuation abi saved **
    armv7a_task_call_stacks abi parked.(TskState) focus
      (task_stack_take parked.(TskState).(parkedTaskStacks) saved.(armv7a_continuation_stack)) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) by entailer! end.
  destruct (armv7a_irq_same_priority_restore_preserves_pending_call external platform port abi sg parked
    saved call (task_set_saved_sp node saved.(armv7a_continuation_sp)) handler focus frame registry_heap
    Hrunning_parked Hschedule Hnonempty Hequal Hbinding Hslice Hcall Hcurrent_parked Hselected eq_refl
    Hparked Haddress_saved Hcovered (Horder registry_heap Hjoint))
    as [exit_heap [Hexit [Hpointers [Hrestore_coverage Hresume]]]].
  assert (Hfocus_after : restored.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { unfold restored, os_int_exit_wrapper_restored_state, os_int_exit_same_priority_state,
      os_int_exit_selection_state, os_int_exit_counter_state.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks replace_IntrS replace_SchedS].
    rewrite task_stack_take_lookup_other; [exact Hretained|].
    rewrite <- Hstack; intro Heq; unfold call in Hnone; rewrite <- Heq in Hnone; congruence. }
  exists registry_heap, exit_heap.
  split; [exact Hwrites|]. split; [exact Hstores|]. split; [exact Hexit|].
  split; [exact Hpointers|]. split; [exact Hrestore_coverage|].
  split; [exact Hfocus_after|exact Hresume].
Qed.

(** TCBInit's Restore prefix, the same-priority IRQ path and BX compose
    without losing the earlier pending call. Ready-list nonemptiness comes
    from the creator's established stage, not a new public requirement. *)
Lemma task_create_tcb_restore_irq_same_priority_preserves_pending_call : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg acquired released node handler suspended publication focus payload
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let returned := os_int_exit_same_priority_state parked in
  let current := os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_create_call_stage call released ->
  armv7a_task_frame_slice suspended ->
  released.(SchedState).(isRunning) = true -> released.(IntrState).(intNesting) = 0 ->
  released.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  released.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
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
  interrupt_exit_requests_schedule true parked.(IntrState) = true ->
  sched_selected_priority parked.(TskState) parked.(SchedState) =
    sched_priority_byte parked.(SchedState).(curSchedPrio) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
   task_tcb_init_stack_context environment call ** kernel_program_inv sg released **
   armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
  (forall written irq_input saved_heap,
    armv7a_restore_prefix_transition restore cursor before written irq_input ->
    armv7a_save_transition abi handler suspended irq_input saved_heap ->
    exists registry_heap exit_heap,
      written = kernel_restore_write_cpsr cursor /\
      kernel_heap_writes (armv7a_continuation_save_writes suspended)
        irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
      kernel_heap_execution (armv7a_irq_live_entry_writes sg released
        call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
        saved_heap registry_heap /\
      os_int_exit_masked_same_priority_fragment sg registry_heap exit_heap /\
      armv7a_irq_restore_pointer_reads sg exit_heap
        (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot))
        suspended.(armv7a_continuation_sp) /\
      task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call /\
      task_create_call_stage (armv7a_continuation_resumed_call suspended call) current /\
      task_stack_live_coverage current.(TskState)
        (task_stack_call_active_key (armv7a_continuation_resumed_call suspended call)) /\
      current.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload /\
      (forall irq_return resume_cursor final_cursor after,
        armv7a_restore_transition abi handler suspended exit_heap irq_return ->
        resume_cursor.(kernel_restore_msr_word) = Some
          (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) ->
        resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
        armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
        final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
        (kernel_call_execution_owned environment.(task_stack_call_external)
           environment.(task_stack_call_platform) (armv7a_continuation_resumed_call suspended call)
           (armv7a_irq_fiq_mask saved) **
         kernel_program_inv sg current **
         armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
         (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
           handler.(os_int_exit_handler_fragments) ** frame)) after)).
Proof.
  intros environment critical arch restore sg acquired released node handler suspended publication
    focus payload saved cursor before frame call abi parked returned current
    Horigin Hstage Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hschedule Hequal Hr0 Hmask Hhandler Hpre
    written irq_input saved_heap Hprefix Hsave.
  match type of Hpre with ?P before => assert (Hrelease : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_program_inv sg released **
     armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold task_tcb_init_stack_context; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region _ _ _ _ restore sg call saved acquired
    cursor before written irq_input _ Hr0 Hmask (Hrelease before Hpre) Hprefix)
    as [Hwritten [Hmemory Hreleased]].
  match type of Hreleased with ?P irq_input => assert (Hirq : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg released **
     armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
     (unmap_table_rep sg ** frame))) end.
  { unfold os_int_exit_frame_save_pre; rewrite Hhandler, kernel_program_inv_split_unmap; entailer!. }
  assert (Hready : task_create_irq_caller_stage call released).
  { eapply task_create_call_stage_irq_entry; eassumption. }
  assert (Hready_parked : task_create_irq_caller_stage call parked).
  { eapply task_create_irq_deposit_preserves_caller_stage; eassumption. }
  assert (Hnonempty : parked.(SchedState).(readyList) <> []).
  { destruct Hready_parked as [_ [ready [Hlookup [Hcurrent_ready [Hgeneration Hready_if]]]]].
    pose proof (proj2 (proj2 (proj1 (interrupt_exit_requests_schedule_iff true parked.(IntrState)) Hschedule)))
      as Hlock.
    destruct (Hready_if Hlock) as [_ [_ [_ [Hin _]]]].
    intro Hnil; rewrite Hnil in Hin; contradiction. }
  destruct (armv7a_irq_source_same_priority_preserves_pending_call _ _ _ abi sg released node handler
    suspended publication focus payload frame irq_input saved_heap
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hschedule Hnonempty Hequal (Hirq irq_input Hreleased) Hsave)
    as [registry_heap [exit_heap [Hwrites [Hstores [Hexit [Hpointers [Hcovered [Hretained Hresume]]]]]]]].
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hsaved_mask Hobserved]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hready_returned : task_create_irq_caller_stage call returned).
  { change (task_create_irq_caller_stage call (os_int_exit_counter_state true parked)).
    apply task_create_irq_counter_exit_preserves_caller_stage; exact Hready_parked. }
  assert (Hstage_current : task_create_call_stage (armv7a_continuation_resumed_call suspended call) current).
  { unfold current; rewrite Hlease; apply task_create_irq_take_reestablishes_call_stage; assumption. }
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call).
  { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    repeat split; assumption || reflexivity. }
  assert (Hactive : task_stack_call_active_key (armv7a_continuation_resumed_call suspended call) =
    Some (task_stack_key suspended.(armv7a_continuation_stack))).
  { unfold task_stack_call_active_key, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin os_sched_call_stack]; rewrite Horigin, Hlease; reflexivity. }
  exists registry_heap, exit_heap.
  split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  split; [exact Hexit|]. split; [exact Hpointers|]. split; [exact Hsame|].
  split; [exact Hstage_current|]. split; [rewrite Hactive; exact Hcovered|].
  split; [exact Hretained|].
  intros irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix.
  destruct (Hresume irq_return Hrestore) as [Hreturned_memory Howned].
  rewrite Hhandler in Hsaved_mask; rewrite Hsaved_mask in Howned.
  match type of Howned with ?P irq_return => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call suspended call)
      (armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
        cursor.(kernel_restore_r0))) **
    (kernel_program_inv sg current **
     armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame))) end.
  { rewrite armv7a_cpsr_restore_mask_eq, Hr0, kernel_program_inv_split_unmap; entailer!. }
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call suspended call)
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))
    resume_cursor irq_return final_cursor after _ Hword (Hsuffix_input irq_return Howned) Hsuffix)
    as [Hcursor [Hfinal_memory Hfinal]].
  split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hfinal.
    match type of Hfinal with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) by entailer! end end.
    exact (Hclose after Hfinal).
Qed.
