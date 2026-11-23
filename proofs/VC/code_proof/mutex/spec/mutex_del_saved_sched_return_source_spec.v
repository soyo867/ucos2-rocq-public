Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected descriptor is the actual saved Del invocation, not the
    foreign call that may have been awakened earlier. At this PRESENT
    selector cut its task is the ready head. The physical producer below
    saves the outgoing task and restores this exact saved invocation.

    OS_Sched's existing modular C join connects its OS_TASK_SW return to
    the later OS_EXIT_CRITICAL call with the same local cpu_sr. The latter
    has its own cursor/LR: no equality with the saved OSCtxSw LR is used.
    The supplied actual Restore prefix/suffix describe the uninterrupted
    branch of that later call, not an assumed eventual public return.

    This consumer ends in the existing [mutex_del_source_return] used by
    Del's annotation. Current readiness, coverage, owner history and the
    private Event pool come from the actual selector/SP/park/take updates.
    No public admission, architecture law or state Record is added. *)
Lemma mutex_del_saved_sched_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg state node context old_sp cpsr values lr prefix suffix first old_words publication
  original saved acquired descriptor focus before (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments original.(os_sched_call_stack) updated in
  let returned := kernel_selected_call descriptor current in
  os_sched_source_live_save_input sg state node context old_sp cpsr values lr
    prefix suffix first old_words focus publication ->
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
     context 192 ** mutex_del_stack_resources sg state **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi context outgoing stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg updated updated ->
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          descriptor.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads descriptor installed /\
        descriptor.(armv7a_continuation_call) = Some original /\
        (forall restored,
          armv7a_task_restore_transition task_abi context descriptor installed restored ->
          forall cursor restore_written middle final_cursor after,
          cursor.(kernel_restore_r0) = saved ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
          final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
          (mutex_del_source_return environment environment.(mutex_del_call_external)
             environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved) ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg state node context old_sp cpsr values lr prefix suffix
    first old_words publication original saved acquired descriptor focus before frame abi fragments outgoing updated
    current returned Hinput Hselected Hparked Hcoverage Hpre.
  pose proof Hinput as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty Hgeometry]]]]]]].
  match type of Hpre with ?P before => assert (Hobserve : P |--
    coq_prop (UCOS2_state_inv sg state /\ mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState) /\ armv7a_continuation_binding descriptor) && TT) end.
  { unfold mutex_del_stack_resources; rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; Intros.
    sep_apply_l_atomic (kernel_saved_sched_call_take_resources _ _ _ abi critical sg original saved acquired
      descriptor state.(TskState) focus state.(TskState).(parkedTaskStacks)
      descriptor.(armv7a_continuation_fragments) Hparked).
    unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec; [|contradiction].
    unfold kernel_saved_sched_call; Intros; entailer!; intros ? ?; exact I. }
  destruct (proj1 (Hobserve before Hpre)) as [Hvalid [Hreachable [Htypes Hbinding]]].
  assert (Hcovered_updated : task_stack_live_coverage updated.(TskState)
    (Some (task_stack_key context.(os_sched_call_stack)))).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    eapply task_stack_save_sp_preserves_coverage; eassumption. }
  assert (Hcovered_current : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks updated.(TskState)
        (task_stack_park_fragments updated.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) fragments))
      original.(os_sched_call_stack)
      (task_stack_park_covers_active updated.(TskState) context.(os_sched_call_stack) fragments Hcovered_updated)). }
  assert (Hreachable_updated : mutex_program_selected_reachable sg updated).
  { eapply mutex_program_source_history_reachable; [exact Hreachable|].
    eapply mutex_program_saved_sp_source with (actor := context.(os_sched_call_invocation)); reflexivity. }
  assert (Hreachable_current : mutex_program_selected_reachable sg current).
  { eapply mutex_program_source_step_reachable; [exact Hreachable_updated|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hevents : current.(EventState) = state.(EventState)).
  { unfold current, os_sched_install_context, updated, os_sched_save_current_sp.
    rewrite Hnode; reflexivity. }
  assert (Hmember : In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)).
  { change (In original.(os_sched_call_stack).(stackLeaseSlot) state.(SchedState).(readyList)).
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    unfold sched_high_ready_consistency in Hhigh; rewrite Hlist in Hhigh.
    assert (head = original.(os_sched_call_stack).(stackLeaseSlot)) by (destruct Hhigh; congruence).
    subst head; left; reflexivity. }
  match type of Hpre with ?P before => assert (Horder : P |--
    kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      context 192 ** kernel_program_inv sg state **
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
      state.(TskState).(parkedTaskStacks) ** (event_private_pool_rep sg state.(EventState) ** frame)) end.
  { unfold mutex_del_stack_resources; entailer!. }
  destruct (kernel_saved_sched_call_live_switch_source _ _ _ abi critical task_abi sg state node context
    old_sp cpsr values lr prefix suffix first old_words publication original saved acquired descriptor focus
    before (event_private_pool_rep sg state.(EventState) ** frame) Hinput Hselected Hparked (Horder before Hpre))
    as [written [stored [Hwrites [Hload [Hstore Hcontinue]]]]].
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook Hhook_source.
  destruct (Hcontinue captured hooked Hcapture Hhook Hhook_source)
    as [installed [Hinstall [Hreads [Hcall [Hsource Hrestore]]]]].
  fold current returned in Hsource, Hrestore.
  assert (Hsource_returned : kernel_call_task_source returned current) by exact Hsource.
  assert (Hlease : descriptor.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hsame : kernel_stack_call_same_call returned original).
  { unfold returned, kernel_selected_call; rewrite Hcall.
    unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hactive : task_stack_call_active_key original = Some (task_stack_key original.(os_sched_call_stack))).
  { assert (Horigin : returned.(os_sched_call_origin) = RunningInvocation
      returned.(os_sched_call_stack).(stackLeaseSlot) returned.(os_sched_call_stack).(stackLeaseGeneration))
      by exact (proj1 Hsource).
    rewrite (proj1 (proj2 Hsame)), (proj2 (proj2 Hsame)) in Horigin.
    unfold task_stack_call_active_key; rewrite Horigin; reflexivity. }
  exists installed; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hcall|].
  intros restored Htask_restore cursor restore_written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Hrestore restored Htask_restore) as [Hresume [Hpc [Hcpsr [Hmemory Howned]]]].
  assert (Howned_current :
    (critical_region_masked environment.(mutex_del_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     os_sched_context_resources environment.(mutex_del_call_external) returned **
     kernel_program_inv sg current **
     armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
     (event_private_pool_rep sg state.(EventState) ** frame)) restored) by exact Howned.
  assert (Hvalid_current : UCOS2_state_inv sg current).
  { match type of Howned with ?P restored => assert (Hvalidity : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hvalidity restored Howned)). }
  assert (Hstage : mutex_del_call_stage returned current).
  { unfold mutex_del_call_stage; rewrite (proj1 Hsource_returned).
    split; [exact Hsource_returned|]. intros Henabled.
    pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid_current))))) as Hready_members.
    destruct (Hready_members _ Hmember) as [ready [Hready [Hrange Heffective]]].
    rewrite (proj2 (proj2 Hsame)); exists ready; auto. }
  match type of Howned_current with ?P restored => assert (Hrestore_input : P |--
    kernel_stack_call_masked abi mutex_del_stack_resources critical sg
      (task_stack_call_active_key original) returned saved acquired current ** frame) end.
  { sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ abi current.(TskState) focus
      current.(TskState).(parkedTaskStacks)).
    unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
    rewrite Hactive, Hevents; entailer!. }
  destruct (kernel_saved_sched_call_return_source (mutex_del_runtime_sched_environment environment)
    mutex_del_stack_resources critical arch restore sg original returned state saved acquired current
    cursor restored restore_written middle final_cursor after frame Hsame Hsource_returned Hr0 Hmask
    (Hrestore_input restored Howned_current) Hprefix Hsuffix) as [Hrun [Hlr [Hclosed Hsched_post]]].
  split; [exact Hrun|]. split; [exact Hlr|].
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { cbn [mutex_del_runtime_sched_environment task_stack_call_continuations].
    unfold mutex_del_source_return, mutex_del_source_return_at, mutex_del_runtime_return_at.
    Exists returned current environment.
    unfold mutex_del_callsite_environment; entailer!. }
  exact (Hclose after Hclosed).
Qed.
