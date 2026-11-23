Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_source_producer_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations PrimitiveComponent SemPendEventReadySource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is the concrete registered SemPost leaf, not a claim that every
    original C Atom is a Post. Its certificate retains actual helper input,
    output and execution. The full C relation is unchanged. *)
Lemma sem_pend_sem_post_body_parked_stacks : forall environment critical sg observer observer_origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_c_step environment critical sg observer observer_origin)
    state before input stopped current after output) first last,
  sem_pend_c_sequence_call_certificate (kernel_program_c_step environment critical sg observer observer_origin)
    (sem_pend_sem_post_c_step_certificate environment critical sg observer observer_origin)
    _ _ _ _ _ _ _ run first last ->
  current.(TskState).(parkedTaskStacks) = state.(TskState).(parkedTaskStacks).
Proof.
  intros environment critical sg observer observer_origin state before input stopped current after output run
    first last Hcertificate.
  induction Hcertificate.
  - reflexivity.
  - destruct H; reflexivity.
  - etransitivity; [exact IHHcertificate2|exact IHHcertificate1].
  - exact IHHcertificate.
Qed.

Lemma sem_pend_sem_post_body_normal_return : forall environment critical sg original
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    state before input stopped current after output) first last,
  sem_pend_c_sequence_call_certificate
    (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    (sem_pend_sem_post_c_step_certificate environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    _ _ _ _ _ _ _ run first last ->
  kernel_call_normal_return original state original current.
Proof.
  intros environment critical sg original state before input stopped current after output run first last Hcertificate.
  pose proof (sem_pend_sem_post_body_parked_stacks environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    _ _ _ _ _ _ _ run first last Hcertificate) as Hmap.
  split.
  - unfold task_tcb_init_stack_same_call; auto.
  - unfold kernel_call_stack_available; rewrite Hmap; auto.
Qed.

(** Unlike the earlier closed-world producer, this one keeps the actual
    active caller key. Its execution/stack resource is the literal helper's
    frame. The saved continuation map is reindexed by the proved wake merge. *)
Lemma sem_pend_sem_post_restore_body : forall environment critical sg original local mask
  actor entry event node returned before after (frame : Assertion),
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller original) original mask entry before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists run : kernel_c_sequence (kernel_program_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      entry before
      (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original mask entry)
      false wake after
      (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original mask wake),
      sem_pend_c_sequence_call_certificate
        (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
        (sem_pend_sem_post_c_step_certificate environment critical sg
          original.(os_sched_call_invocation) original.(os_sched_call_origin))
        _ _ _ _ _ _ _ run original.(os_sched_call_origin) original.(os_sched_call_origin) /\
      kernel_call_normal_return original entry original wake /\
      flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original mask wake after.
Proof.
  intros environment critical sg original local mask actor entry event node returned before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  set (abi := environment.(task_stack_call_continuations)).
  set (stacks := store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks)).
  set (execution := kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) original mask).
  assert (Hopen : flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller original) original mask entry |--
    coq_prop (UCOS2_state_inv sg entry /\ task_stack_live_coverage entry.(TskState)
      (task_stack_call_active_key original)) &&
    (kernel_program_fields_inv sg entry ** stacks ** (execution ** frame))).
  { rewrite (proj1 (flag_pend_task_save_input_closed_equiv environment critical local (fun _ _ => frame)
      sg original mask entry)).
    assert (Hshuffle : (execution ** (kernel_program_fields_inv sg entry ** stacks)) ** frame |--
      kernel_program_fields_inv sg entry ** stacks ** (execution ** frame)) by entailer!.
    intros heap [closed [rest [Houter [[running [world [Hinner [Hrunning [Hcoverage Hworld]]]]] Hframe]]]].
    split.
    - destruct Hworld as [fields [parked [Hjoin [[Hvalid Hfields] Hparked]]]].
      exact (conj Hvalid Hcoverage).
    - apply (Hshuffle heap); exists closed, rest; split; [exact Houter|].
      split; [|exact Hframe]. exists running, world; exact (conj Hinner (conj Hrunning Hworld)). }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Hworld].
  assert (Hsplit : kernel_program_fields_inv sg entry ** stacks ** (execution ** frame) |--
    EX selected old, coq_prop (event_task_rdy_entry sg entry.(TskState) event node selected old) &&
      (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
        (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** (execution ** frame)))).
  { assert (Hgrouped : kernel_program_fields_inv sg entry ** stacks ** (execution ** frame) |--
      kernel_program_fields_inv sg entry ** (stacks ** (execution ** frame))) by entailer!.
    intros heap Hheap.
    destruct (Hgrouped heap Hheap) as [fields [rest [Hjoin [Hfields Hrest]]]].
    destruct (sem_pend_event_ready_fields_split sg entry event node Hvalid Hlookup Htype Hgroup Hlayout
      fields ((proj1 (kernel_program_fields_inv_split_unmap sg entry)) fields Hfields))
      as [selected [old [Hentry Hready]]].
    exists selected, old; split; [exact Hentry|].
    assert (Hshuffle : (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
      sem_pend_event_ready_fields_frame sg entry event selected) ** (stacks ** (execution ** frame)) |--
      WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
        (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** (execution ** frame))) by entailer!.
    apply (Hshuffle heap); exists fields, rest; exact (conj Hjoin (conj Hready Hrest)). }
  destruct (Hsplit before Hworld) as [selected [old [Hentry Howned]]].
  set (residual := sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** (execution ** frame)).
  assert (Hselected : flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
      (FlagPendTaskCaller original) original mask entry |--
    WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual).
  { intros heap Hheap.
    destruct (Hopen heap Hheap) as [_ Hresources].
    destruct (Hsplit heap Hresources) as [other [previous [Hother Hraw]]].
    destruct (sem_pend_event_ready_entry_unique sg entry.(TskState) event node selected old other previous
      Hentry Hother) as [-> ->].
    exact Hraw. }
  pose proof (sem_post_waiter_source_post sg entry.(TskState) event node selected old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) returned before after residual
    Howned Hactual) as Hpost.
  set (wake := event_wake_state sg entry event node selected old PendSem 0 PendOK).
  assert (Hclose : WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
      residual |-- flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original mask wake).
  { assert (Hjoined : WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK returned **
        residual |-- kernel_continuation_call_closed abi kernel_program_fields_inv local sg
          (task_stack_call_active_key original) original mask wake ** frame).
    { pose proof (sem_pend_event_ready_fields_merge_continuations environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) abi sg entry event node
      selected old returned local (task_stack_call_active_key original)
      Hvalid Hlookup Htype Hentry Hcoverage) as Hjoin.
      cbn zeta in Hjoin; unfold residual, stacks, wake; sepcon_assoc_change; sep_apply_l_atomic Hjoin.
      unfold kernel_continuation_call_closed, kernel_continuation_inv, execution, abi; entailer!. }
    intros heap Hheap.
    apply (proj2 (flag_pend_task_save_input_closed_equiv environment critical local (fun _ _ => frame)
      sg original mask wake)).
    exact (Hjoined heap Hheap). }
  pose (body := @WakeComponent.KernelWakeCEventSegment sg entry event node selected old PendSem 0 PendOK
    returned residual before after Hlookup Hentry Howned Hpost).
  pose (step := @KernelProgramCWake environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ body).
  pose (atom := @KernelCSequenceAtom (kernel_program_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) _ _ _ _ _ _ _ step).
  pose (run := @KernelCSequenceAdapt (kernel_program_c_step environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) _ _ _ _ _ _ _ _ _
    Hpre Hselected atom Hclose).
  assert (Hcertificate : sem_pend_c_sequence_call_certificate
    (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    (sem_pend_sem_post_c_step_certificate environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    _ _ _ _ _ _ _ run original.(os_sched_call_origin) original.(os_sched_call_origin)).
  { unfold run; apply SemPendCSequenceCallAdapt.
    unfold atom; apply SemPendCSequenceCallAtom.
    unfold step, body; econstructor; eassumption. }
  exists selected, old, run; split; [exact Hcertificate|]. split.
  - eapply sem_pend_sem_post_body_normal_return; exact Hcertificate.
  - exact (Hclose after Hpost).
Qed.

(** A nontrivial, state-changing Restore instance. The literal SemPost
    body supplies both its receipt and normal-return observation here.
    No phase output, final owner, or future receipt is a premise. *)
Lemma sem_pend_sem_post_restore_c_sequence : forall environment critical sg original phase local mask saved
  acquired checkpoint actor event node returned arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  cursor before written prefix_heap environment_heap final_cursor after (frame : Assertion),
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup checkpoint event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group checkpoint node <> 0 -> event_object_layout_prop sg event ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
    mask saved acquired checkpoint ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written prefix_heap ->
  sem_post_waiter_execution sg (event_addr sg event) returned prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor after ->
  exists selected old,
    let wake := event_wake_state sg checkpoint event node selected old PendSem 0 PendOK in
    exists completed : kernel_c_sequence (kernel_program_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)) checkpoint before
      (sem_pend_clear_status_phase_restore_input phase environment local critical sg original
        mask saved acquired checkpoint ** frame) false wake after
      (sem_pend_clear_status_phase_restore_output phase environment local critical sg original mask checkpoint ** frame),
      sem_pend_c_sequence_call_certificate
        (kernel_program_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
        (sem_pend_restore_c_leaf_certificate environment critical sg original
          (sem_pend_sem_post_c_step_certificate environment critical sg
            original.(os_sched_call_invocation) original.(os_sched_call_origin)))
        _ _ _ _ _ _ _ completed original.(os_sched_call_origin) original.(os_sched_call_origin) /\
      ((coq_prop (sem_pend_client_return_source environment critical sg original checkpoint original wake /\
          sem_pend_clear_status_phase_restore_observation phase environment critical sg original checkpoint original wake) &&
        sem_pend_fields_closed environment local sg original mask wake) ** frame) after /\
      (sem_pend_clear_status_phase_restore_output phase environment local critical sg original mask checkpoint ** frame) after.
Proof.
  intros environment critical sg original phase local mask saved acquired checkpoint actor event node returned arch
    restore cursor before written prefix_heap environment_heap final_cursor after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hr0 Hmask Hpre Hprefix Hpost Hsuffix.
  pose (leaf := sem_pend_sem_post_c_step_certificate environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  destruct (sem_pend_client_restore_prefix_c_sequence environment critical sg original leaf
    phase local mask saved acquired checkpoint arch restore cursor before written prefix_heap frame
    Hr0 Hmask Hpre Hprefix) as [prefix [Hprefix_certificate [Hmiddle Hword]]].
  destruct (sem_pend_sem_post_restore_body environment critical sg original local (armv7a_irq_fiq_mask saved)
    actor checkpoint event node returned prefix_heap environment_heap frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hmiddle Hpost)
    as [selected [old [body [Hcertificate [Hnormal Howner]]]]].
  exists selected, old.
  eapply (sem_pend_client_restore_c_sequence environment critical sg original leaf)
    with (body := body) (restore := restore) (cursor := cursor) (written := written)
      (final_cursor := final_cursor).
  - exact (sem_pend_sem_post_c_step_client_calls environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  - exact Hr0.
  - exact Hmask.
  - exact Hpre.
  - exact Hprefix.
  - exact Hcertificate.
  - exact Hnormal.
  - exact Hsuffix.
Qed.
