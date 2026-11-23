Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_status Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One actual foreign C segment while a Del invocation is parked:
    OSSemPend writes Stat, StatPend and Dly, then OS_EventTaskWait writes
    EventPtr and the ready/wait bitmaps. The same heap endpoint supplies
    both the registered client edge and the current canonical Restore
    input. Other saved calls retain their exact descriptor-local owners.

    [task_holds_no_mutex] is the existing MutexProgramWait application
    protocol, not a new condition on Del's public precondition. Likewise,
    registration and a distinct actor identify this particular foreign
    execution; they do not assert that every client is a Wait operation.

    This is a finite source segment, not an eventual-return theorem.
    Its endpoint precedes the foreign caller's first Restore. The real
    Restore/Save and subsequent OS_Sched call keep their existing modular
    contracts. No register-save geometry or new platform law is used. *)
Lemma mutex_del_foreign_wait_continuation_source :
  forall environment critical saved_local sg observer context mask saved
    entry eid event tid old timeout (frame : Assertion) before,
  let action := mutex_program_operation_client (Some context.(os_sched_call_invocation))
    (MutexProgramWait eid tid event old PendSem timeout) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  critical.(critical_region_clients) action ->
  context.(os_sched_call_invocation) <> observer ->
  sem_pend_wait_entry sg entry eid event tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_holds_no_mutex entry.(EventState) tid ->
  interrupt_saved_value mask saved ->
  0 <= timeout < 4294967296 ->
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg
    (task_stack_call_active_key context) context saved entry entry ** frame) before ->
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid old timeout before waited /\
    kernel_client_step action sg entry waiting /\
    kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
      context.(os_sched_call_origin) entry false context.(os_sched_call_origin) waiting /\
    mutex_owner_source_history sg entry waiting /\
    kernel_call_task_source context waiting /\
    sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
    waiting.(TskState).(parkedTaskStacks) = entry.(TskState).(parkedTaskStacks) /\
    waiting.(SchedState).(readyList) = remove_Z_eqb tid entry.(SchedState).(readyList) /\
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key context) context saved entry waiting ** frame) waited /\
    (sem_pend_continuation_restore_input environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (Some environment) critical saved_local
      sg context mask saved entry waiting ** unmap_table_rep sg **
      event_private_pool_rep sg waiting.(EventState) ** frame) waited.
Proof.
  intros environment critical saved_local sg observer context mask saved entry eid event tid old
    timeout frame before action waiting Hregistered Hforeign Hentry Hsource Hcache Hno_mutex
    Hsaved Htimeout Hpre.
  set (abi := environment.(task_stack_call_continuations)).
  set (local := task_create_continuation_local saved_local).
  set (active := task_stack_call_active_key context).
  pose proof Hentry as [Hvalid [_ [Hcurrent [Hnode [Hevent _]]]]].
  set (rest :=
    critical_region_masked environment.(task_stack_call_platform) critical sg
      context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
    os_sched_context_resources environment.(task_stack_call_external) context **
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) ** unmap_table_rep sg **
    event_private_pool_rep sg entry.(EventState) ** frame).
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg entry /\
      mutex_del_private_types_non_mutex entry.(EventState) /\
      task_stack_live_coverage entry.(TskState) active) &&
    (sem_pend_wait_prefix_cells sg entry tid old (encode_task_status old.(stat))
      (encode_pend_status old.(statPend)) old.(dly) ** rest)) end.
  { unfold kernel_continuation_call_masked, kernel_continuation_inv,
      mutex_del_stack_resources, rest, abi, local, active.
    rewrite kernel_program_inv_split_unmap.
    Intros.
    sep_apply_l_atomic (sem_pend_wait_prefix_split sg entry tid old Hvalid Hcurrent Hnode).
    unfold sem_pend_wait_prefix_cells; entailer!. }
  destruct (Hopen before Hpre) as [[Hreachable [Htypes Hcoverage]] Hcells].
  destruct (sem_pend_wait_stores_source sg entry eid event tid old timeout rest before
    Hentry Htimeout Hcells) as [waited [Hstores Hafter]].
  assert (Hstep : kernel_client_step action sg entry waiting).
  { unfold action, mutex_program_operation_client, mutex_program_operation; cbn.
    split; [exact Hevent|]. split; [exact Hnode|].
    split; [exact Hno_mutex|reflexivity]. }
  assert (Hhistory : mutex_owner_source_history sg entry waiting).
  { apply mutex_owner_source_step_history; apply MutexOwnerSourceWait;
      [exact Hevent|exact Hno_mutex]. }
  assert (Hregistered_source : kernel_client_task_source_trace
      environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None
      context.(os_sched_call_origin) entry false context.(os_sched_call_origin) waiting).
  { change (kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
      context.(os_sched_call_origin) entry
      (orb (kernel_client_stops action observer) false) context.(os_sched_call_origin) waiting).
    eapply KernelClientTaskSourceStep with (action := action) (transient := waiting)
      (middle := context.(os_sched_call_origin)).
    - exact Hregistered.
    - unfold action; cbn [mutex_program_operation_client kernel_client_actor]; congruence.
    - intros invocation Hnone; discriminate.
    - exact Hstep.
    - eapply TaskExecutionClientFrame; [exact Hstep|reflexivity].
    - constructor. }
  assert (Hreachable_after : mutex_program_selected_reachable sg waiting).
  { eapply mutex_program_source_history_reachable; eassumption. }
  assert (Htypes_after : mutex_del_private_types_non_mutex waiting.(EventState)).
  { change (mutex_del_private_types_non_mutex entry.(EventState)); exact Htypes. }
  assert (Hpool : event_private_pool_rep sg waiting.(EventState) =
    event_private_pool_rep sg entry.(EventState)) by reflexivity.
  pose proof (sem_pend_wait_preserves_call_source sg context entry eid event tid old timeout
    Hentry Hsource Hcache) as [Hvalid_after [Hsource_after Hcache_after]].
  assert (Hmerge : sem_pend_wait_call_post sg entry eid event tid old timeout ** rest |--
    kernel_continuation_call_masked abi mutex_del_stack_resources local critical sg active
      context saved entry waiting ** frame).
  { eapply derivable1_trans with (y :=
      (critical_region_masked environment.(task_stack_call_platform) critical sg
        context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
       os_sched_context_resources environment.(task_stack_call_external) context **
       sem_pend_wait_call_post sg entry eid event tid old timeout **
       store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
         entry.(TskState).(parkedTaskStacks)) **
      (unmap_table_rep sg ** event_private_pool_rep sg entry.(EventState) ** frame)).
    { unfold rest; entailer!. }
    sep_apply_l_atomic (sem_pend_wait_call_continuation_merge_source
      environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi local critical sg active context saved entry
      eid event tid old timeout Hentry Hsource Hcache Hcoverage).
    fold waiting.
    unfold kernel_continuation_call_masked, kernel_continuation_inv, mutex_del_stack_resources.
    rewrite kernel_program_inv_split_unmap, Hpool; entailer!. }
  pose proof (Hmerge waited Hafter) as Hworld.
  exists waited; split; [exact Hstores|]. split; [exact Hstep|].
  split; [exact Hregistered_source|]. split; [exact Hhistory|].
  split; [exact Hsource_after|]. split; [exact Hcache_after|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hworld|].
  match type of Hworld with ?P waited => match goal with |- ?Q waited =>
    assert (Hcanonical : P |-- Q) end end.
  { unfold sem_pend_continuation_restore_input, sem_pend_optional_continuation_resources,
      task_tcb_init_continuation_capsules, kernel_continuation_call_masked,
      kernel_continuation_inv, mutex_del_stack_resources, abi, local, active.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  exact (Hcanonical waited Hworld).
Qed.

(** The next genuine Scheduler C prefix, after the foreign caller's
    Restore and Scheduler Save contracts have supplied its current
    masked owner. The waiting state is the exact endpoint above; no
    returning world is assumed. This finite family has the parked
    observer immediately after the foreign task in the ready order.

    Removing the foreign task exposes that observer as the actual next
    selection. Current-cache consistency proves that the C byte guard
    requests a switch. The active key's absence comes from the earlier
    install/take map, transported by the real registration/wait cuts; it
    is not deduced from abstract execution authority or a new ABI law.

    The result stops at OS_TASK_SW. It neither applies the C frame rule
    across arbitrary foreign execution nor asserts that this port call
    returns. Its existing generic install/return consumer can use this
    exact selector state once the port contract supplies the saved item. *)
Lemma mutex_del_foreign_wait_scheduler_prefix :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local critical sg context saved acquired entry eid event tid old timeout
    outgoing outgoing_fragments incoming hooked next tail (frame : Assertion) before,
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  sem_pend_wait_entry sg entry eid event tid old ->
  entry.(SchedState).(readyList) = tid :: next :: tail ->
  entry.(TskState).(parkedTaskStacks) =
    (os_sched_install_context outgoing outgoing_fragments incoming hooked).(TskState).(parkedTaskStacks) ->
  context.(os_sched_call_stack) = incoming ->
  kernel_call_task_source context waiting ->
  sched_current_consistency waiting.(TskState) waiting.(SchedState) ->
  os_sched_selection_enabled waiting = true ->
  (kernel_continuation_call_masked abi mutex_del_stack_resources local critical sg
    (task_stack_call_active_key context) context saved acquired waiting ** frame) before ->
  exists after,
    os_sched_source_switch_prefix_execution sg before after /\
    os_sched_requests_switch waiting = true /\
    checkpoint.(SchedState).(highRdyTid) = Some next /\
    sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState) /\
    checkpoint.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None /\
    kernel_call_task_source context checkpoint /\
    mutex_owner_source_history sg waiting checkpoint /\
    (kernel_continuation_call_masked abi mutex_del_stack_resources local critical sg
      (task_stack_call_active_key context) context saved acquired checkpoint ** frame) after.
Proof.
  intros external platform port abi local critical sg context saved acquired entry eid event tid old timeout
    outgoing outgoing_fragments incoming hooked next tail frame before waiting checkpoint
    Hentry Hready_order Htaken_map Hlease Hsource Hcache Henabled Hpre.
  pose proof Hentry as [Hvalid_entry [_ [Hcurrent _]]].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid_entry)))) as Hentry_ready.
  pose proof (proj2 (proj2 (proj2 Hentry_ready))) as Hnodup.
  assert (Hdifferent : next <> tid).
  { rewrite Hready_order in Hnodup.
    inversion Hnodup as [|head rest Hnotin Htail]; subst.
    intro Heq; subst next; apply Hnotin; left; reflexivity. }
  assert (Hwaiting_order : waiting.(SchedState).(readyList) =
    next :: remove_Z_eqb tid tail).
  { change (remove_Z_eqb tid entry.(SchedState).(readyList) = next :: remove_Z_eqb tid tail).
    rewrite Hready_order; apply remove_Z_eqb_x_then_ne_cons.
    apply Z.eqb_neq; exact Hdifferent. }
  assert (Hnonempty : waiting.(SchedState).(readyList) <> []).
  { rewrite Hwaiting_order; discriminate. }
  assert (Hwaiting_valid : UCOS2_state_inv sg waiting).
  { apply sem_pend_wait_entry_preserves_validity; exact Hentry. }
  assert (Hslot : context.(os_sched_call_stack).(stackLeaseSlot) = tid).
  { pose proof (proj1 (kernel_call_task_source_current_at context waiting Hsource)) as Hpointer.
    change (entry.(SchedState).(curTaskID) = Some context.(os_sched_call_stack).(stackLeaseSlot)) in Hpointer.
    congruence. }
  assert (Hswitch : os_sched_requests_switch waiting = true).
  { destruct (os_sched_requests_switch waiting) eqn:Hbranch; [reflexivity|].
    destruct (os_sched_nonswitch_current_ready_at sg context waiting Hwaiting_valid Hsource Hcache
      Henabled Hbranch Hnonempty) as [node [Hready Hgeneration]].
    destruct Hready as [_ [_ [_ [Hmember _]]]].
    pose proof (proj1 (os_sched_ready_checkpoint_frame waiting)) as Hrdy.
    change (In context.(os_sched_call_stack).(stackLeaseSlot)
      (os_sched_ready_checkpoint waiting).(readyList)) in Hmember.
    rewrite Hrdy, Hslot in Hmember.
    change (In tid (remove_Z_eqb tid entry.(SchedState).(readyList))) in Hmember.
    exfalso; exact (remove_Z_eqb_notin tid entry.(SchedState).(readyList) Hmember). }
  assert (Habsent : checkpoint.(TskState).(parkedTaskStacks)
    (task_stack_key context.(os_sched_call_stack)) = None).
  { change (entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None).
    rewrite Htaken_map, Hlease; apply task_stack_take_lookup. }
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg waiting /\
      mutex_del_private_types_non_mutex waiting.(EventState)) &&
    (kernel_continuation_call_masked abi kernel_program_inv local critical sg
      (task_stack_call_active_key context) context saved acquired waiting **
      (event_private_pool_rep sg waiting.(EventState) ** frame))) end.
  { unfold kernel_continuation_call_masked, kernel_continuation_inv,
      mutex_del_stack_resources; entailer!. }
  destruct (Hopen before Hpre) as [[Hreachable Htypes] Hmasked].
  destruct (os_sched_modular_prefix_continuation_resources external platform port abi local critical sg
    (task_stack_call_active_key context) context saved acquired waiting before
    (event_private_pool_rep sg waiting.(EventState) ** frame) (fun _ => Hnonempty) Hmasked)
    as [after [Hprefix [Hhigh Hafter]]].
  unfold os_sched_modular_prefix_execution in Hprefix; rewrite Hswitch in Hprefix.
  specialize (Hhigh Hswitch); fold checkpoint in Hhigh, Hafter.
  assert (Hselected : checkpoint.(SchedState).(highRdyTid) = Some next).
  { unfold sched_high_ready_consistency in Hhigh.
    pose proof (proj1 (os_sched_ready_checkpoint_frame waiting)) as Hrdy.
    assert (Hcheckpoint_order : checkpoint.(SchedState).(readyList) =
      next :: remove_Z_eqb tid tail).
    { change ((os_sched_ready_checkpoint waiting).(readyList) = next :: remove_Z_eqb tid tail).
      rewrite Hrdy; exact Hwaiting_order. }
    rewrite Hcheckpoint_order in Hhigh; exact (proj1 Hhigh). }
  assert (Hhistory : mutex_owner_source_history sg waiting checkpoint).
  { apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hreachable_after : mutex_program_selected_reachable sg checkpoint).
  { eapply mutex_program_source_history_reachable; eassumption. }
  exists after; split; [exact Hprefix|]. split; [exact Hswitch|]. split; [exact Hselected|].
  split; [exact Hhigh|]. split; [exact Habsent|]. split.
  - apply os_sched_prefix_preserves_task_source; exact Hsource.
  - split; [exact Hhistory|].
    match type of Hafter with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) end end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv, mutex_del_stack_resources.
      change checkpoint.(EventState) with waiting.(EventState); entailer!. }
    exact (Hclose after Hafter).
Qed.
