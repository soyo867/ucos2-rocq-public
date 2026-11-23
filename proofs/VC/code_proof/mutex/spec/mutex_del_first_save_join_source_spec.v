Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_recycle_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_call_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_recheck_reuse_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_sched_return_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_foreign_entry_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The first IRQ writes this exact SP into the original task's TCB.
    These facts will be transported through the foreign execution; the
    returning Save never assumes a new, independently chosen saved SP. *)
Local Lemma mutex_del_first_irq_pending_fields : forall sg entry call node saved,
  entry.(SchedState).(isRunning) = true ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active entry.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) ->
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  task_invocation_active parked.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
  task_saved_pointer_at parked call.(os_sched_call_stack) saved.(armv7a_continuation_sp) /\
  mutex_owner_source_history sg entry parked.
Proof.
  intros sg entry call node saved Hrunning Hnode Hgen Hactive parked.
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node saved.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  split.
  - rewrite Htasks; change (task_invocation_active
      (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp node saved.(armv7a_continuation_sp)))
      call.(os_sched_call_invocation) call.(os_sched_call_origin)).
    eapply task_set_saved_sp_preserves_invocation_active; eassumption.
  - split.
    + exists (task_set_saved_sp node saved.(armv7a_continuation_sp)); split.
      * rewrite Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
        rewrite Z.eqb_refl; reflexivity.
      * split; [exact Hgen|reflexivity].
    + eapply mutex_program_task_fields_source with
        (tid := call.(os_sched_call_stack).(stackLeaseSlot))
        (old := node) (new := task_set_saved_sp node saved.(armv7a_continuation_sp));
        [exact Hnode|reflexivity|reflexivity|rewrite Htasks; reflexivity|].
      unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
        armv7a_irq_entry_counter_state, os_sched_save_current_sp.
      rewrite Hrunning; cbn [replace_IntrS EventState TskState]; rewrite Hnode; reflexivity.
Qed.

Local Lemma mutex_del_critical_preserves_pending_fields : forall sg eid option before result after original lease sp,
  mutex_del_critical sg eid option before result after ->
  task_invocation_active before.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at before lease sp ->
  task_invocation_active after.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  task_saved_pointer_at after lease sp /\ mutex_owner_source_history sg before after.
Proof.
  intros sg eid option before result after original lease sp Hcritical Hactive Hpointer.
  destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hcritical)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  assert (Hlookup : forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
    exists node, after.(TskState).(inUsedTaskStates) slot = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbStkPtr) = old.(tcbStkPtr)).
  { intros slot old Hold; specialize (Hnodes slot); rewrite Hold in Hnodes.
    destruct (after.(TskState).(inUsedTaskStates) slot) as [node|] eqn:Hnode;
      cbn in Hnodes; [|discriminate].
    injection Hnodes as Hg Hsp; exists node; auto. }
  split.
  - destruct Hactive as [Hinv [Hret Hlive]]; unfold task_invocation_active; rewrite Hlife.
    split; [exact Hinv|]. split; [exact Hret|].
    destruct original.(os_sched_call_origin) as [|slot generation]; [exact I|].
    destruct Hlive as [old [Hold Hg]].
    destruct (Hlookup _ _ Hold) as [node [Hnode [Hgen Hsp]]].
    exists node; split; [exact Hnode|congruence].
  - split.
    + destruct Hpointer as [old [Hold [Hg Hsp]]].
      destruct (Hlookup _ _ Hold) as [node [Hnode [Hgen Hvalue]]].
      exists node; split; [exact Hnode|]; split; congruence.
    + eapply mutex_program_del_critical_source; exact Hcritical.
Qed.

(** The next IRQ overwrites only the currently executing foreign TCB's
    SP. The original focus is present and the foreign key absent, so their
    live slots differ. This proves preservation from the SAME heap cut. *)
Local Lemma mutex_del_foreign_irq_preserves_pending_fields : forall sg entry original suspended foreign node saved,
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  entry.(SchedState).(isRunning) = true ->
  entry.(TskState).(inUsedTaskStates) foreign.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = foreign.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key foreign.(os_sched_call_stack)) = None ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  let parked := armv7a_irq_live_parked_state entry foreign saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  task_invocation_active parked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  task_saved_pointer_at parked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
  mutex_owner_source_history sg entry parked.
Proof.
  intros sg entry original suspended foreign node saved Hbinding Hcall Hactive Hpointer Hrunning Hnode
    Hgen Hnone Hfocus parked.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hdifferent : suspended.(armv7a_continuation_stack).(stackLeaseSlot) <>
    foreign.(os_sched_call_stack).(stackLeaseSlot)).
  { intros Heq; destruct Hpointer as [old [Hold [Hg Hsp]]].
    rewrite Heq in Hold; assert (old = node) by congruence; subst old.
    assert (Hkey : task_stack_key foreign.(os_sched_call_stack) = task_stack_key original.(os_sched_call_stack)).
    { rewrite <- Hlease; unfold task_stack_key; congruence. }
    rewrite Hkey in Hnone; congruence. }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) foreign.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node saved.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) foreign.(os_sched_call_stack)
      saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  split.
  - rewrite Htasks; change (task_invocation_active
      (glob_task_set_usedtask entry.(TskState) foreign.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp node saved.(armv7a_continuation_sp)))
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
    eapply task_set_saved_sp_preserves_invocation_active; eassumption.
  - split.
    + destruct Hpointer as [old [Hold [Hg Hsp]]]; exists old; split; [|auto].
      rewrite Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
      destruct (Z.eqb _ _) eqn:Heq; [apply Z.eqb_eq in Heq; contradiction|exact Hold].
    + eapply mutex_program_task_fields_source with
        (tid := foreign.(os_sched_call_stack).(stackLeaseSlot))
        (old := node) (new := task_set_saved_sp node saved.(armv7a_continuation_sp));
        [exact Hnode|reflexivity|reflexivity|rewrite Htasks; reflexivity|].
      unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
        armv7a_irq_entry_counter_state, os_sched_save_current_sp.
      rewrite Hrunning; cbn [replace_IntrS EventState TskState]; rewrite Hnode; reflexivity.
Qed.

(** A single physical creator trace supplies both the mutated ECB owner
    and the original invocation's live registration/SP. The selected
    return below consumes that same registry heap. *)
Local Lemma mutex_del_foreign_recycle_pending_registry : forall environment critical actor creator sg
  initial original suspended eid event prepared node handler saved publication before saved_heap (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  let parked := armv7a_irq_live_parked_state checkpoint call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  valid_event_id sg eid ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  mutex_owner_source_history sg initial checkpoint ->
  task_invocation_active checkpoint.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at checkpoint suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  armv7a_task_frame_slice saved ->
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
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened checkpoint.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) saved.(armv7a_continuation_sp) ->
  (forall action, mutex_del_creator_source_client actor creator action -> critical.(critical_region_clients) action) ->
  actor <> Some original.(os_sched_call_invocation) -> mutex_del_creator_arguments creator ->
  (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
     call handler.(os_int_exit_interrupted_mask) **
   mutex_del_focused_world abi sg focus payload (Some (task_stack_key call.(os_sched_call_stack))) checkpoint **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg checkpoint
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall next after,
      kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
        KernelClientHeapClosed registry_heap next after ->
      exists returned returned_origin kind,
        kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
          KernelClientHeapClosed parked next returned /\
        kernel_resumption_task_source_trace environment.(mutex_del_call_external) environment.(mutex_del_call_port)
          critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
          original.(os_sched_call_origin) parked false returned_origin returned /\
        mutex_owner_source_history sg initial returned /\
        task_invocation_active returned.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
        task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
        (forall current, returned.(EventState).(inUsedEventStates) eid = Some current ->
          current.(eventType) <> OS_EVENT_TYPE_MUTEX) /\
        uchar_load (event_addr sg eid) kind after /\
        mutex_del_runtime_type_observation sg eid returned kind /\ kind <> 4 /\
        (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed returned **
          (interrupt_platform_running environment.(mutex_del_call_platform)
             handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
           os_int_exit_context_resources environment.(mutex_del_call_port) handler ** frame)) after).
Proof.
  intros environment critical actor creator sg initial original suspended eid event prepared node handler saved
    publication before saved_heap frame abi call focus payload checkpoint parked Hid Hbinding Hcall Hhistory
    Hactive Hpointer Hslice Hrunning Hnest Hcurrent Hnode Hnode_id Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hinclude Hforeign Harguments Hpre Hsave.
  assert (Hfocus : checkpoint.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = Some payload).
  { match type of Hpre with ?P before => assert (Hexpose : P |--
      coq_prop (checkpoint.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) && TT) end.
    { unfold mutex_del_focused_world; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hpre)). }
  destruct (mutex_del_foreign_irq_preserves_pending_fields sg checkpoint original suspended call node saved
    Hbinding Hcall Hactive Hpointer Hrunning Hnode Hgen Hnone Hfocus)
    as [Hparked_active [Hparked_pointer Hparked_history]].
  match type of Hpre with ?P before => assert (Hirq_pre : P |--
    os_int_exit_frame_save_pre environment.(mutex_del_call_external) environment.(mutex_del_call_platform) handler **
    (mutex_del_focused_world abi sg focus payload (Some (task_stack_key call.(os_sched_call_stack))) checkpoint ** frame))
      by (unfold os_int_exit_frame_save_pre, call; entailer!) end.
  destruct (mutex_del_foreign_irq_registry _ _ _ abi sg checkpoint node handler saved publication focus payload frame
    before saved_heap Hslice Hrunning Hnest Hcurrent Hnode Hnode_id Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp (Hirq_pre before Hpre) Hsave) as [registry_heap [Hwrites [Hstores Hregistry]]].
  assert (Hvalid : UCOS2_state_inv sg parked).
  { match type of Hregistry with ?P registry_heap => assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold mutex_del_stack_registry, kernel_client_call_stack_resources, kernel_client_call_stack_world.
      rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose registry_heap Hregistry)). }
  assert (Hevent : parked.(EventState) = checkpoint.(EventState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS EventState TskState]; rewrite Hnode; reflexivity. }
  assert (Hnonmutex : forall current, parked.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) <> OS_EVENT_TYPE_MUTEX).
  { intros current Hget; rewrite Hevent in Hget.
    unfold checkpoint in Hget; cbn [mutex_del_always_checkpoint mutex_del_recycle_state replace_EventS
      EventState event_recycle inUsedEventStates] in Hget.
    rewrite kernel_map_set_same in Hget; discriminate. }
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros next after Htrace.
  destruct (mutex_del_creator_trace_saved_pointer _ _ _ abi critical.(critical_region_clients) actor creator
    sg original.(os_sched_call_invocation) focus payload suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) KernelClientHeapClosed registry_heap next after _ Hinclude Hforeign Harguments
    Htrace parked original.(os_sched_call_origin) I Hparked_pointer Hregistry)
    as [returned [returned_origin [Hstates [Hsource [Hcut [Hreturned_pointer Hafter]]]]]].
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource)) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    parked returned Hinterval Hvalid) as [Hreturned_valid [Hcreation Hactive_preserved]].
  assert (Hnonmutex_returned : forall current, returned.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) <> OS_EVENT_TYPE_MUTEX)
    by (eapply mutex_del_creator_trace_preserves_non_mutex_slot; eassumption).
  destruct (mutex_del_registry_non_mutex_type_load _ _ _ abi sg focus payload next returned eid after _ Hid
    (mutex_del_creator_trace_preserves_return_cut creator sg _ _ _ _ Hstates I) Hnonmutex_returned Hafter)
    as [kind [Hload [Hobs [Hkind Hclosed]]]].
  exists returned, returned_origin, kind; split; [exact Hstates|]. split; [exact Hsource|]. split.
  - eapply mutex_owner_source_history_trans; [exact Hhistory|].
    eapply mutex_owner_source_history_trans; [exact Hparked_history|].
    eapply mutex_del_creator_trace_owner_history; exact Hstates.
  - split; [apply Hactive_preserved; exact Hparked_active|]. split; [exact Hreturned_pointer|].
    split; [exact Hnonmutex_returned|]. split; [exact Hload|]. split; [exact Hobs|]. split; assumption.
Qed.

(** The first real IRQ supplies the original descriptor/SP. Selection of
    a different initial frame then establishes the foreign caller that
    executes Del below, while preserving the pending original call. The
    initial-frame fact is extracted from the same owned selected frame. *)
Lemma mutex_del_first_irq_initial_call_source : forall environment
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (entry_abi : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg entry node handler suspended publication (frame : Assertion) before saved_heap,
  let original := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original handler.(os_int_exit_interrupted_pc) suspended.(armv7a_continuation_lr) in
  let payload := (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  let parked := armv7a_irq_live_parked_state entry original suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  armv7a_task_frame_slice suspended ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = original.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  valid_task_stack_region original.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range original.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range original.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  os_int_exit_requests_switch true parked = true -> parked.(SchedState).(readyList) <> [] ->
  (forall slot current_node, (os_int_exit_ready_checkpoint true parked).(SchedState).(highRdyTid) = Some slot ->
    parked.(TskState).(inUsedTaskStates) slot = Some current_node ->
    (slot, current_node.(taskGeneration)) <> task_stack_key original.(os_sched_call_stack)) ->
  kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true parked) (os_int_exit_ready_checkpoint true parked) ->
  (os_int_exit_frame_save_pre environment.(mutex_del_call_external) environment.(mutex_del_call_platform) handler **
    (kernel_stack_inv abi mutex_del_stack_resources sg
      (Some (task_stack_key original.(os_sched_call_stack))) entry ** frame)) before ->
  armv7a_save_transition abi handler suspended before saved_heap ->
  armv7a_continuation_binding suspended /\ suspended.(armv7a_continuation_call) = Some original /\
  suspended.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
  exists registry_heap selected_heap,
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      original.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    os_int_exit_source_switch_prefix_execution sg registry_heap selected_heap /\
    (forall hooked, kernel_heap_execution [] selected_heap hooked ->
      exists transfer installed selected,
        transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true parked /\
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
        (forall restored,
          selected.(armv7a_continuation_call) = None ->
          task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
            0 selected.(armv7a_continuation_fragments) ->
          armv7a_restore_transition abi handler selected installed restored ->
          let state := os_int_exit_installed_state transfer in
          let foreign := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
            selected.(armv7a_continuation_fragments) in
          let registered := armv7a_initial_call_registered selected state in
          os_int_exit_source_selected_execution environment.(mutex_del_call_external)
            environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi
            sg parked handler transfer selected registry_heap restored /\
          mutex_owner_source_history sg entry registered /\
          task_invocation_active registered.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
          task_saved_pointer_at registered suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
          mutex_del_call_stage foreign registered /\ registered.(IntrState).(intNesting) = 0 /\
          (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
             foreign (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
           mutex_del_focused_world abi sg focus payload (task_stack_call_active_key foreign) registered **
           (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) restored)).
Proof.
  intros environment task_abi initial entry_abi sg entry node handler suspended publication frame before saved_heap
    original abi focus payload parked Hactive Hslice Hrunning Hnest Hcurrent Hnode Hnode_id Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hswitch Hnonempty Hdifferent Hhook Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hsaved_mask [Hpc [Hsaved_sp Hfragments]]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  destruct (mutex_del_first_irq_pending_fields sg entry original node suspended Hrunning Hnode Hgen Hactive)
    as [Hparked_active [Hparked_pointer Hhistory]].
  destruct (mutex_del_stack_irq_entry _ _ _ abi sg entry node handler suspended publication frame before saved_heap
    Hslice Hrunning Hnest Hcurrent Hnode Hnode_id Hgen Hnone (Haddress _) Hregion Hgeometry Hpublication Hsp Hpre Hsave)
    as [registry_heap [Hwrites [Hstores Hregistry]]].
  assert (Hparked_running : parked.(SchedState).(isRunning) = true).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState SchedState]; rewrite Hnode; exact Hrunning. }
  destruct (mutex_del_irq_foreign_selected_source _ _ _ abi task_abi initial sg parked focus
    suspended.(armv7a_continuation_fragments) handler registry_heap frame Hparked_running Hswitch Hnonempty
    Hdifferent Haddress Hhook Hregistry) as [selected_heap [Hprefix Hselect]].
  split; [exact Hbinding|]. split; [exact Hcall|]. split; [exact Hpc|].
  exists registry_heap, selected_heap; split; [exact Hwrites|]. split; [exact Hstores|]. split; [exact Hprefix|].
  intros hooked Hempty.
  destruct (Hselect hooked Hempty) as [transfer [installed [selected [selected_node
    [Hstate [Hinstall [Hinitial Hreturn]]]]]]].
  exists transfer, installed, selected; split; [exact Hstate|]. split; [exact Hinstall|].
  intros restored Hinitial_call Hinitial_geometry Hrestore state foreign registered.
  destruct (Hreturn restored Hrestore) as [Hexecution [Hreachable [Htypes [Hzero [Hlookup Howned]]]]].
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Howned with ?P restored => assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold os_sched_source_selected_post, UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose restored Howned)). }
  assert (Hregistered_active : task_invocation_active registered.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { apply task_begin_invocation_preserves_invocation_active.
    - pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto.
    - unfold state, os_int_exit_installed_state; rewrite Hstate; exact Hparked_active. }
  assert (Hregistered_pointer : task_saved_pointer_at registered suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { rewrite Hlease; change (task_saved_pointer_at state original.(os_sched_call_stack)
      suspended.(armv7a_continuation_sp)).
    unfold state, os_int_exit_installed_state; rewrite Hstate; exact Hparked_pointer. }
  assert (Hregistered_history : mutex_owner_source_history sg entry registered).
  { eapply mutex_owner_source_history_trans; [exact Hhistory|].
    apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame;
      unfold registered, armv7a_initial_call_registered, state, os_int_exit_installed_state;
      rewrite Hstate; reflexivity. }
  match type of Howned with ?P restored => assert (Hregister : P |--
    coq_prop (mutex_del_call_stage foreign registered /\ registered.(IntrState).(intNesting) = 0) &&
    (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
       foreign (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
     mutex_del_focused_world abi sg focus payload (task_stack_call_active_key foreign) registered **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))) end.
  { eapply derivable1_trans with (y :=
      (os_sched_source_selected_post environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
        environment.(mutex_del_call_port) abi sg focus transfer.(os_int_exit_incoming_stack)
        selected selected_node state ** unmap_table_rep sg ** event_private_pool_rep sg state.(EventState)) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)).
    - entailer!.
    - eapply derivable1_trans.
      + apply derivable1_sepcon_mono.
        * exact (mutex_del_selected_initial_focused_entry environment entry_abi sg focus payload
            transfer.(os_int_exit_incoming_stack) selected selected_node state (Hinitial Hinitial_call)
            Hinitial_call Hinitial_geometry Hreachable Htypes Hzero Hlookup).
        * reflexivity.
      + cbv zeta; entailer!. }
  destruct (Hregister restored Howned) as [[Hstage Hzero_registered] Hregistered].
  exact (conj Hexecution (conj Hregistered_history (conj Hregistered_active
    (conj Hregistered_pointer (conj Hstage (conj Hzero_registered Hregistered)))))).
Qed.

Section RecycledFirstSaveReturn.
Context (environment : MutexDelCallEnvironment) (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner
      environment.(mutex_del_call_platform) environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).

(** The creator trace starts on the heap produced by the foreign task's
    actual IRQ. Its original-call identity, saved SP and owner history feed
    the selected original-frame return on THAT heap. The final non-Mutex
    guard is the observed protected C branch; other guards remain separate
    source families. No returned heap or invocation is chosen independently. *)
Lemma mutex_del_foreign_delete_reuse_error_source : forall critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  actor creator initial entry original suspended saved_word eid event mutex prepared node handler saved publication
  before saved_heap option perr old_error cpu_sr foreign_registers foreign_final_registers acquired
  foreign_before foreign_saved foreign_body foreign_prepared foreign_recycled cursor written middle
  final_cursor foreign_returned foreign_perr foreign_old_error foreign_cpu_sr (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  let retained := (foreign_perr # UChar |-> 0) **
    (foreign_cpu_sr # UInt |-> foreign_registers.(kernel_save_cpsr)) ** frame in
  mutex_del_parent_layout sg ->
  valid_event_id sg eid -> mutex_del_parent_prefix_ok (event_addr sg eid) initial eid ->
  mutex_del_parent_entry sg eid entry event mutex -> mutex_del_call_stage call entry ->
  mutex_del_parent_prefix_ok (event_addr sg eid) entry eid ->
  encode_event_wait_grp event.(waitList) entry.(TskState) = 0 ->
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  foreign_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr foreign_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask foreign_registers.(kernel_save_cpsr) = handler.(os_int_exit_interrupted_mask) ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  suspended.(armv7a_continuation_pc) = armv7a_save_entry_address save + 4 ->
  nth 0 suspended.(armv7a_continuation_registers) 0 = saved_word ->
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word ->
  mutex_owner_source_history sg initial entry ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  armv7a_task_frame_slice saved ->
  checkpoint.(SchedState).(isRunning) = true -> checkpoint.(IntrState).(intNesting) = 0 ->
  checkpoint.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  checkpoint.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  checkpoint.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened checkpoint.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) saved.(armv7a_continuation_sp) ->
  (forall action, mutex_del_creator_source_client actor creator action -> critical.(critical_region_clients) action) ->
  actor <> Some original.(os_sched_call_invocation) -> mutex_del_creator_arguments creator ->
  (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
     call handler.(os_int_exit_interrupted_mask) **
   mutex_del_focused_world abi sg focus payload (task_stack_call_active_key call) entry **
   ((foreign_perr # UChar |-> foreign_old_error) ** (foreign_cpu_sr # UInt |->_) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame)))) foreign_before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr foreign_registers) entry foreign_before
    foreign_final_registers acquired foreign_saved ->
  kernel_heap_execution (pointer_store_writes foreign_cpu_sr foreign_final_registers.(kernel_save_r0))
    foreign_saved foreign_body ->
  mutex_del_prepare_source_execution sg (event_addr sg eid) eid entry prepared foreign_body foreign_prepared ->
  mutex_del_always_after_prepare_execution sg (event_addr sg eid) foreign_prepared foreign_recycled ->
  cursor.(kernel_restore_r0) = foreign_final_registers.(kernel_save_r0) ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor foreign_recycled written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor foreign_returned ->
  kernel_heap_execution [(foreign_perr, 0)] foreign_returned before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg checkpoint
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall next creator_heap,
      kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
        KernelClientHeapClosed registry_heap next creator_heap ->
      exists state observed_kind,
        task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
        task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
        uchar_load (event_addr sg eid) observed_kind creator_heap /\ observed_kind <> 4 /\
        (state.(SchedState).(isRunning) = true -> os_int_exit_requests_switch true state = true ->
         state.(SchedState).(readyList) <> [] ->
         (os_int_exit_ready_checkpoint true state).(SchedState).(highRdyTid) =
           Some original.(os_sched_call_stack).(stackLeaseSlot) ->
         kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg
           (os_int_exit_ready_checkpoint true state) (os_int_exit_ready_checkpoint true state) ->
         exists selected_heap installed selected,
           os_int_exit_source_switch_prefix_execution sg creator_heap selected_heap /\
           sched_install_heap_fragment sg selected_heap installed
             (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
           (forall irq_return registers final_registers acquired resumed stored kind,
             armv7a_restore_transition abi handler selected installed irq_return ->
             registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
             registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
             registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
             armv7a_save_suffix_transition save registers
               (os_int_exit_wrapper_restored_state
                 (replace_SchedS (sched_install_selected (os_int_exit_ready_checkpoint true state).(SchedState))
                   (os_int_exit_ready_checkpoint true state)) original.(os_sched_call_stack))
               irq_return final_registers acquired resumed ->
             kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) resumed stored ->
             uchar_load (event_addr sg eid + OSEventType_off) kind stored ->
             kind <> 4 /\
             exists observed actual,
               mutex_del_runtime_type_observation sg eid observed kind /\
               mutex_del_runtime_save_facts sg (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
                 saved_word initial observed /\ kernel_stack_call_same_call actual original /\
               (forall restore_entry cursor written released returned final restored final_cursor exited after,
                 cursor.(kernel_restore_r0) = saved_word ->
                 armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
                 armv7a_restore_prefix_transition restore cursor stored written released ->
                 mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
                   environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi sg Local local_step normal_return
                   handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments)
                   (armv7a_irq_fiq_mask saved_word) (restore_entry + 8) cursor.(kernel_restore_lr)
                   actual observed released returned final restored ->
                 armv7a_restore_suffix_transition restore written restored final_cursor exited ->
                 kernel_heap_execution [(perr, encode_os_err_code OS_ERR_EVENT_TYPE)] exited after ->
                 final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
                 (mutex_del_runtime_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
                    sg original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) initial
                    (event_addr sg eid) option eid (event_addr sg eid) (encode_os_err_code OS_ERR_EVENT_TYPE) **
                  (perr # UChar |-> encode_os_err_code OS_ERR_EVENT_TYPE) ** (cpu_sr # UInt |-> saved_word) **
                  task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** retained) after)))).
Proof.
  intros critical arch save restore actor creator initial entry original suspended saved_word eid event mutex prepared node
    handler saved publication before saved_heap option perr old_error cpu_sr foreign_registers foreign_final_registers
    acquired foreign_before foreign_saved foreign_body foreign_prepared foreign_recycled cursor written middle
    final_cursor foreign_returned foreign_perr foreign_old_error foreign_cpu_sr frame abi call focus payload checkpoint retained
    Hlayout Hid Hprefix Hparent Hstage Hforeign_prefix Hwait Hforeign_origin Hforeign_return Hforeign_valid Hforeign_mask
    Horigin Hbinding Hcall Hslice Hpc Hr0 Hsaved Hhistory Hactive Hpointer Hforeign_slice Hrunning Hnest
    Hcurrent Hnode Hnode_id Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hinclude Hforeign Harguments Hpre
    Hforeign_save Hforeign_store Hprepare Hbody Hcursor Hmasked Hrestore_prefix Hrestore_suffix Herror Hsave.
  destruct (mutex_del_foreign_local_delete_post environment critical arch save restore sg focus payload call
    handler.(os_int_exit_interrupted_mask) entry eid event mutex foreign_registers foreign_final_registers acquired prepared
    foreign_before foreign_saved foreign_body foreign_prepared foreign_recycled cursor written middle final_cursor
    foreign_returned before foreign_perr foreign_old_error foreign_cpu_sr
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
      ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame))
    Hlayout Hid Hparent Hstage Hforeign_prefix Hwait Hforeign_return Hforeign_valid Hforeign_mask Hpre
    Hforeign_save Hforeign_store Hprepare Hbody Hcursor Hmasked Hrestore_prefix Hrestore_suffix Herror)
    as [Hacquired [Hforeign_execution [Hcritical [Hstage_after [Hdeleted Hforeign_public]]]]].
  destruct (mutex_del_critical_preserves_pending_fields sg eid 1 entry (0, (OS_ERR_NONE, false)) checkpoint
    original suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hcritical Hactive Hpointer)
    as [Hactive_checkpoint [Hpointer_checkpoint Hdelete_history]].
  assert (Hhistory_checkpoint : mutex_owner_source_history sg initial checkpoint)
    by (eapply mutex_owner_source_history_trans; eassumption).
  assert (Hkey : task_stack_call_active_key call = Some (task_stack_key call.(os_sched_call_stack))).
  { unfold task_stack_call_active_key; rewrite Hforeign_origin; reflexivity. }
  rewrite Hkey in Hdeleted.
  match type of Hdeleted with ?P before => assert (Hreorder : P |--
    kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      call handler.(os_int_exit_interrupted_mask) **
    mutex_del_focused_world abi sg focus payload (Some (task_stack_key call.(os_sched_call_stack))) checkpoint **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** retained))
    by (unfold retained; entailer!) end.
  destruct (mutex_del_foreign_recycle_pending_registry environment critical actor creator sg initial original
    suspended eid event prepared node handler saved publication before saved_heap
    ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** retained)
    Hid Hbinding Hcall Hhistory_checkpoint Hactive_checkpoint Hpointer_checkpoint Hforeign_slice Hrunning Hnest
    Hcurrent Hnode Hnode_id Hgen Hnone (Haddress _) Hregion Hgeometry Hpublication Hsp Hinclude Hforeign Harguments
    (Hreorder before Hdeleted) Hsave)
    as [registry_heap [Hwrites [Hstores Htrace]]].
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros next creator_heap Hcreator.
  destruct (Htrace next creator_heap Hcreator)
    as [state [returned_origin [kind [Hstates [Hsource [Hhistory' [Hactive' [Hpointer'
      [Hnonmutex [Hload [Hobservation [Hkind Hregistry]]]]]]]]]]]].
  exists state, kind; split; [exact Hactive'|]. split; [exact Hpointer'|].
  split; [exact Hload|]. split; [exact Hkind|].
  intros Hrunning' Hswitch Hnonempty Hhigh Hhook.
  destruct (mutex_del_first_save_irq_return_source environment critical arch save sg initial state handler original
    suspended saved_word creator_heap ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** retained)
    Horigin Hbinding Hcall Hslice Hpc Hr0 Hsaved Hhistory' Hactive' Hpointer' Hrunning' Hswitch Hnonempty Hhigh
    Hhook (Haddress _) Hregistry)
    as (selected_heap & installed & selected & Hselect & Hempty & Hinstall & Hcpsr & Hvalues & Hfocus & Hentry & Hreturn).
  exists selected_heap, installed, selected; split; [exact Hselect|]. split; [exact Hinstall|].
  intros irq_return registers final_registers original_acquired resumed stored protected_kind Hirq Hreg0 Hregcpsr Hreglr
    Hsuffix Hstore Htype.
  destruct (Hreturn irq_return registers final_registers original_acquired resumed Hirq Hreg0 Hregcpsr Hreglr Hsuffix)
    as [Horiginal_acquired [Hword [Hlr [Hreturned Hreturned_masked]]]].
  rewrite Hword in Hstore.
  set (current := os_int_exit_wrapper_restored_state
    (replace_SchedS (sched_install_selected (os_int_exit_ready_checkpoint true state).(SchedState))
      (os_int_exit_ready_checkpoint true state)) original.(os_sched_call_stack)) in *.
  (** These are two logical views of the same actual cpu_sr store. The
      deterministic heap equation keeps the exact current Event owner
      and the public Save post tied to that single execution. *)
  match type of Hreturned_masked with ?P resumed => assert (Hmasked_store : P |-- (cpu_sr # UInt |->_) **
    (kernel_stack_call_masked abi mutex_del_stack_resources critical sg (task_stack_call_active_key original)
       (armv7a_continuation_resumed_call selected original) saved_word current current **
     (perr # UChar |-> old_error) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** retained))
    by entailer! end.
  destruct (task_stack_uint_store_execution cpu_sr saved_word _ resumed (proj1 Hsaved)
    (Hmasked_store resumed Hreturned_masked)) as [written_heap [Hwrite Hwritten_masked]].
  assert (written_heap = stored) by (eapply kernel_heap_execution_deterministic; eassumption); subst written_heap.
  match type of Hwritten_masked with ?P stored => assert (Htype_owner : P |--
    coq_prop (mutex_del_private_types_non_mutex current.(EventState)) &&
    (kernel_program_inv sg current ** event_private_pool_rep sg current.(EventState) ** TT)) end.
  { unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
    entailer!; intros ? ?; exact I. }
  destruct (Htype_owner stored Hwritten_masked) as [Htypes Howned_type].
  assert (Hnonmutex_current : forall found, current.(EventState).(inUsedEventStates) eid = Some found ->
    found.(eventType) <> OS_EVENT_TYPE_MUTEX) by exact Hnonmutex.
  destruct (mutex_del_non_mutex_slot_type_load sg current eid stored _ Hid Htypes Hnonmutex_current Howned_type)
    as [read_kind [Hread [_ Hread_not]]].
  replace (event_addr sg eid + OSEventType_off) with (event_addr sg eid) in Htype by
    (unfold OSEventType_off; lia).
  assert (Hequal_kind : read_kind = protected_kind) by
    (eapply uchar_load_deterministic; [exact Hread|exact Htype]).
  assert (Hnot : protected_kind <> 4) by congruence.
  split; [exact Hnot|].
  match type of Hreturned with ?P resumed => assert (Hstore_pre : P |-- (cpu_sr # UInt |->_) **
    (mutex_del_source_save_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
       critical sg original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial **
     (perr # UChar |-> old_error) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** retained))
    by entailer! end.
  destruct (task_stack_uint_store_execution cpu_sr saved_word _ resumed (proj1 Hsaved) (Hstore_pre resumed Hreturned))
    as [produced [Hwrite_return Hwritten]].
  assert (produced = stored) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  match type of Hwritten with ?P stored => assert (Hrecheck_pre : P |--
    mutex_del_source_save_post environment environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
       critical sg original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial **
     (perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved_word) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** retained)
    by entailer! end.
  apply (mutex_del_recheck_error_source_post environment sg Local local_step normal_return handler_contract
    handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) critical arch restore original
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) saved_word initial (event_addr sg eid) eid option protected_kind
    perr old_error cpu_sr stored retained eq_refl Hid Hprefix (Hrecheck_pre stored Hwritten)); [|exact Hnot].
  replace (event_addr sg eid + OSEventType_off) with (event_addr sg eid) by (unfold OSEventType_off; lia).
  exact Htype.
Qed.
End RecycledFirstSaveReturn.
