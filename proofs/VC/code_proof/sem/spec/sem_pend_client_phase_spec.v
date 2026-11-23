Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_runtime_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_return_resources_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Local phase information for the existing Timer Task caller. It uses
    that caller's established Task/Idle/available entry and does not
    replace the public generic Sem admission. Readiness is kept separate
    while this caller is registered as a waiter. *)
Definition sem_pend_client_phase_context sg call state : Prop :=
  UCOS2_state_inv sg state /\ kernel_call_task_source call state /\
  state.(SchedState).(isRunning) = true /\ kernel_running_idle_ready sg state /\
  kernel_call_stack_available call state /\
  sched_current_consistency state.(TskState) state.(SchedState).

Definition sem_pend_client_phase_wait_at environment critical sg original mask initial observed eid timeout
  waiting call current : Prop :=
  kernel_stack_call_same_call call original /\
  sem_pend_client_wait_history environment critical sg original mask initial observed eid timeout waiting /\
  sem_pend_client_wait_source environment critical sg original eid
    original.(os_sched_call_stack).(stackLeaseGeneration) waiting current /\
  exists node, current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node.

Definition sem_pend_client_phase_selected_at environment critical sg original mask initial observed eid timeout
  waiting call current : Prop :=
  sem_pend_client_phase_wait_at environment critical sg original mask initial observed eid timeout
    waiting call current /\
  exists node, sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) node.

Definition sem_pend_client_phase_save_pre phase environment critical sg call mask before : Prop :=
  sem_pend_client_phase_context sg call before /\
  match phase with
  | SemPendAcquirePhase pevent eid observed =>
      sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent before eid observed /\
      pevent <> 0 /\ sem_pend_context_error (event_slot_type_value before.(EventState) eid)
        before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
      sem_pend_task_call_stage sg call before
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\ sem_pend_client_phase_selected_at environment critical sg original initial_mask
        initial observed eid timeout waiting call before
  | SemPendReturnPhase => False
  end.

Definition sem_pend_client_phase_save_observation phase environment critical sg call returned mask saved
  before acquired : Prop :=
  sem_pend_client_phase_context sg returned acquired /\
  match phase with
  | SemPendAcquirePhase pevent eid observed =>
      exists current, sem_pend_client_acquire_observation environment critical sg call returned mask saved
        before acquired eid observed current /\
        sem_pend_task_call_stage sg call acquired /\ sem_pend_blocking_call_stage sg call acquired
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\ sem_pend_client_phase_selected_at environment critical sg original initial_mask
        initial observed eid timeout waiting returned acquired
  | SemPendReturnPhase => False
  end.

Definition sem_pend_client_phase_save_input phase environment local critical sg call mask before : Assertion :=
  coq_prop (sem_pend_client_phase_save_pre phase environment critical sg call mask before) &&
  sem_pend_fields_closed environment local sg call mask before.

Definition sem_pend_client_phase_save_output phase environment local critical sg call mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (sem_pend_client_return_source environment critical sg call before returned acquired /\
      interrupt_saved_value mask saved /\ sem_pend_save_rely sg before acquired /\
      sem_pend_client_phase_save_observation phase environment critical sg call returned mask saved before acquired) &&
    sem_pend_fields_masked environment local critical sg returned saved acquired acquired.

Definition sem_pend_client_phase_restore_pre phase environment critical sg call mask checkpoint : Prop :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      mask = initial_mask /\ sem_pend_client_phase_context sg call checkpoint /\
      sem_pend_client_phase_wait_at environment critical sg original initial_mask initial observed
        eid timeout waiting call checkpoint
  | SemPendReturnPhase => sem_pend_task_call_stage sg call checkpoint /\
      kernel_running_idle_ready sg checkpoint /\ kernel_call_stack_available call checkpoint
  | SemPendAcquirePhase _ _ _ => False
  end.

Definition sem_pend_client_phase_restore_observation phase environment critical sg call checkpoint returned current : Prop :=
  match phase with
  | SemPendWaitPhase original initial_mask initial observed eid timeout waiting =>
      sem_pend_client_phase_context sg returned current /\
      sem_pend_client_phase_wait_at environment critical sg original initial_mask initial observed
        eid timeout waiting returned current
  | SemPendReturnPhase => sem_pend_client_task_return_observation sg call checkpoint returned current
  | SemPendAcquirePhase _ _ _ => False
  end.

Definition sem_pend_client_phase_restore_input phase environment local critical sg call mask saved acquired
  checkpoint : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\
    sem_pend_client_phase_restore_pre phase environment critical sg call mask checkpoint) &&
  sem_pend_fields_masked environment local critical sg call saved acquired checkpoint.

Definition sem_pend_client_phase_restore_output phase environment local critical sg call mask checkpoint : Assertion :=
  EX returned current,
    coq_prop (sem_pend_client_return_source environment critical sg call checkpoint returned current /\
      sem_pend_client_phase_restore_observation phase environment critical sg call checkpoint returned current) &&
    sem_pend_fields_closed environment local sg returned mask current.

Lemma sem_pend_client_phase_context_from_task_stage : forall sg call state,
  UCOS2_state_inv sg state -> sem_pend_task_call_stage sg call state ->
  kernel_running_idle_ready sg state -> kernel_call_stack_available call state ->
  sem_pend_client_phase_context sg call state.
Proof.
  intros sg call state Hvalid [Hsource [Hrunning [node [Hready Hrest]]]] Hidle Havailable.
  exact (conj Hvalid (conj Hsource (conj Hrunning (conj Hidle (conj Havailable
    (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready)))))).
Qed.

Lemma sem_pend_client_phase_context_return : forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  sem_pend_client_phase_context sg call before -> sem_pend_client_phase_context sg returned after.
Proof.
  intros environment critical sg call before returned after Hreturn
    [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]].
  destruct (sem_pend_client_return_source_preserves_runtime environment critical sg call before returned after
    Hreturn Hvalid Hsource Hrunning Hidle Hcache) as [Hvalid' [Hrunning' [Hidle' Hcache']]].
  pose proof (proj2 (sem_pend_client_return_source_restore_observation _ _ _ _ _ _ _ Hreturn)
    Hvalid Hsource) as Hsource'.
  destruct Hreturn as [Htrace Hnormal].
  exact (conj Hvalid' (conj Hsource' (conj Hrunning' (conj Hidle' (conj (proj2 Hnormal Havailable) Hcache'))))).
Qed.

Lemma sem_pend_client_phase_wait_at_initial : forall environment critical sg original mask initial observed
  eid timeout waiting call,
  kernel_stack_call_same_call call original ->
  sem_pend_client_wait_history environment critical sg original mask initial observed eid timeout waiting ->
  sem_pend_client_phase_wait_at environment critical sg original mask initial observed eid timeout waiting call waiting.
Proof.
  intros * Hsame Hhistory; split; [exact Hsame|]. split; [exact Hhistory|].
  split; [apply sem_pend_client_wait_source_refl|].
  exact (sem_pend_client_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hhistory).
Qed.

Lemma sem_pend_client_phase_wait_at_return : forall environment critical sg original mask initial observed
  eid timeout waiting call before returned after,
  sem_pend_client_phase_wait_at environment critical sg original mask initial observed eid timeout waiting call before ->
  UCOS2_state_inv sg before ->
  sem_pend_client_return_source environment critical sg call before returned after ->
  kernel_call_task_source call before -> kernel_call_task_source returned after ->
  sem_pend_client_phase_wait_at environment critical sg original mask initial observed eid timeout waiting returned after.
Proof.
  intros * [Hsame [Hhistory [Hpath [node [Hnode Hwait]]]]] Hvalid Hreturn Htask Hafter.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hreturn) as Hreturned.
  assert (Hnode_call : before.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { rewrite (proj2 (proj2 Hsame)); exact Hnode. }
  destruct (sem_pend_client_return_source_waiter_projection environment critical sg call before returned after
    node eid _ Hreturn Hvalid Htask Hafter Hnode_call Hwait) as [next [Hnext Heffects]].
  rewrite (proj2 (proj2 Hsame)) in Hnext.
  split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Hhistory|]. split.
    + eapply SemPendClientWaitTrans; [exact Hpath|]. eapply SemPendClientWaitReturn; eassumption.
    + exists next; split; [exact Hnext|]. eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

Lemma sem_pend_client_phase_selected_from_member : forall environment critical sg original mask initial observed
  eid timeout waiting call current,
  sem_pend_client_phase_wait_at environment critical sg original mask initial observed eid timeout waiting call current ->
  sem_pend_client_phase_context sg call current ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  sem_pend_client_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call current.
Proof.
  intros * Hwait [Hvalid [Hsource Hrest]] Hmember; split; [exact Hwait|].
  destruct Hwait as [Hsame [Hhistory [Hpath [node [Hnode Hcont]]]]].
  destruct (kernel_call_task_source_current_at call current Hsource) as [Hcurrent Hfound].
  rewrite (proj2 (proj2 Hsame)) in Hcurrent.
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) _ Hmember)
    as [ready [Hready [_ Heffective]]].
  assert (ready = node) by congruence; subst ready.
  destruct (sem_pend_wait_ready_resume_registration _ _ _ Hcont Heffective) as [Hregistration Hgeneration].
  exists node; unfold sem_pend_resume_entry; auto.
Qed.

Lemma sem_pend_client_phase_selected_resume_origin : forall environment critical sg original mask initial observed
  eid timeout waiting call current,
  sem_pend_client_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call current ->
  exists node, sem_pend_client_resume_origin environment critical sg original mask initial observed eid timeout
    current original.(os_sched_call_stack).(stackLeaseSlot) node.
Proof.
  intros * [[Hsame [Hhistory [Hpath [node [Hnode Hcont]]]]] [selected Hselected]].
  pose proof Hselected as [Hvalid [Hcurrent [Hselected_node Hrest]]].
  assert (selected = node) by congruence; subst selected.
  pose proof (proj1 Hcont) as Hgeneration.
  pose proof Hhistory as [_ [Hsource _]].
  exists node; split; [exact Hselected|]. split.
  - rewrite Hgeneration; exact (proj1 Hsource).
  - exists waiting; split; [exact Hhistory|]. rewrite Hgeneration; exact Hpath.
Qed.

Lemma sem_pend_client_return_source_refl : forall environment critical sg call state,
  sem_pend_client_return_source environment critical sg call state call state.
Proof.
intros; split; [apply sem_pend_observed_client_trace_refl|apply kernel_call_normal_return_refl].
Qed.

Lemma sem_pend_client_phase_save_observations : forall phase environment critical sg call returned mask saved before acquired,
  sem_pend_client_phase_save_pre phase environment critical sg call mask before ->
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  interrupt_saved_value mask saved -> sem_pend_save_rely sg before acquired ->
  interrupt_in_range acquired.(IntrState) ->
  sem_pend_client_phase_save_observation phase environment critical sg call returned mask saved before acquired.
Proof.
  intros phase environment critical sg call returned mask saved before acquired
    [Hcontext Hpre] Hreturn Hsaved Hrely Hrange.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  split; [exact Hafter|]. destruct phase as [pevent eid observed|original initial_mask initial observed eid timeout waiting|].
  - destruct Hcontext as [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]].
    destruct Hpre as [Hinput [Hnonnull [Hclear Hstage]]].
    destruct (sem_pend_client_acquire_observation_from_input environment critical sg call returned pevent eid observed
      mask saved before acquired Hreturn Hvalid Hinput Hnonnull Hclear Hsaved) as [current Hobservation].
    assert (Hguards : before.(IntrState).(intNesting) <= 0 /\ before.(IntrState).(lockNesting) <= 0).
    { change ((if negb (Z.eqb (event_slot_type_value before.(EventState) eid) 3)
        then Some OS_ERR_EVENT_TYPE else
        if Z.ltb 0 before.(IntrState).(intNesting) then Some OS_ERR_PEND_ISR else
        if Z.ltb 0 before.(IntrState).(lockNesting) then Some OS_ERR_PEND_LOCKED else None) = None) in Hclear.
      destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3) in Hclear;
        cbn [negb] in Hclear; [|discriminate].
      destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hint in Hclear; [discriminate|].
      destruct (Z.ltb 0 before.(IntrState).(lockNesting)) eqn:Hlock in Hclear; [discriminate|].
      apply Z.ltb_ge in Hint; apply Z.ltb_ge in Hlock; auto. }
    exists current; split; [exact Hobservation|].
    exact (sem_pend_client_save_blocking_call_stage environment critical sg call before returned acquired
      Hreturn Hvalid Hstage Hidle Havailable (proj1 Hguards) (proj2 Hguards) Hrange Hrely).
  - destruct Hpre as [Hmask [Hwait [old Hentry]]].
    split; [exact Hmask|].
    pose proof (sem_pend_client_phase_wait_at_return environment critical sg original initial_mask initial observed
      eid timeout waiting call before returned acquired Hwait (proj1 Hcontext) Hreturn
      (proj1 (proj2 Hcontext)) (proj1 (proj2 Hafter))) as Hwait'.
    pose proof Hentry as [_ [Hcurrent [_ [_ Hmember]]]].
    eapply sem_pend_client_phase_selected_from_member; [exact Hwait'|exact Hafter|].
    exact (proj2 (proj2 (proj2 Hrely)) _ Hcurrent Hmember).
  - contradiction.
Qed.

(** A packaging consumer. The concrete producers below obtain this
    masked owner from their actual ABI execution, never from an Ensure
    which already asserts this desired phase output. *)
Lemma sem_pend_client_phase_save_output_intro : forall phase environment local critical sg call returned
  mask saved before acquired,
  sem_pend_client_phase_save_pre phase environment critical sg call mask before ->
  sem_pend_client_return_source environment critical sg call before returned acquired ->
  interrupt_saved_value mask saved -> sem_pend_save_rely sg before acquired ->
  sem_pend_fields_masked environment local critical sg returned saved acquired acquired |--
  sem_pend_client_phase_save_output phase environment local critical sg call mask saved before.
Proof.
  intros * Hpre Hreturn Hsaved Hrely heap Howner.
  pose proof (sem_pend_fields_masked_observations environment local critical sg returned saved acquired acquired
    heap Howner) as [Hvalid Hrange].
  pose proof (sem_pend_client_phase_save_observations _ _ _ _ _ _ _ _ _ _ Hpre Hreturn Hsaved Hrely Hrange) as Hphase.
  exists returned, acquired; split; [exact (conj Hreturn (conj Hsaved (conj Hrely Hphase)))|exact Howner].
Qed.

Lemma sem_pend_client_phase_uninterrupted_save : forall phase environment local critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch)
  sg call state mask registers before final_registers acquired after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_client_phase_save_input phase environment local critical sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before final_registers acquired after ->
  acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (sem_pend_client_phase_save_output phase environment local critical sg call mask final_registers.(kernel_save_r0)
    state ** frame) after.
Proof.
  intros phase environment local critical arch save sg call state mask registers before final_registers acquired after
    frame Hcursor Hvalid Hmask Hinput Hactual.
  assert (Hpre : sem_pend_client_phase_save_pre phase environment critical sg call mask state).
  { assert (Hobserve : sem_pend_client_phase_save_input phase environment local critical sg call mask state ** frame |--
      coq_prop (sem_pend_client_phase_save_pre phase environment critical sg call mask state)).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exact Hfact. } exact (Hobserve before Hinput). }
  assert (Hclosed : (sem_pend_fields_closed environment local sg call mask state ** frame) before).
  { assert (Hforget : sem_pend_client_phase_save_input phase environment local critical sg call mask state ** frame |--
      sem_pend_fields_closed environment local sg call mask state ** frame).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exists owned, rest; exact (conj Hjoin (conj Howner Hframe)). } exact (Hforget before Hinput). }
  destruct (kernel_continuation_call_uninterrupted_save _ _ _ _ arch environment.(task_stack_call_continuations)
    save kernel_program_fields_inv local sg (task_stack_call_active_key call) call state mask registers before
    final_registers acquired after frame Hcursor Hvalid Hmask Hclosed Hactual)
    as [Hstate [Hvalue [Hexecution Howner]]].
  assert (Hsaved : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hvalue; split; assumption. }
  assert (Hrely : sem_pend_save_rely sg state state).
  { unfold sem_pend_save_rely, kernel_call_control_rely; auto. }
  pose proof (sem_pend_client_phase_save_output_intro phase environment local critical sg call call mask
    final_registers.(kernel_save_r0) state state Hpre
    (sem_pend_client_return_source_refl environment critical sg call state) Hsaved Hrely) as Hpack.
  assert (Hframe : sem_pend_fields_masked environment local critical sg call final_registers.(kernel_save_r0)
      state state ** frame |--
    sem_pend_client_phase_save_output phase environment local critical sg call mask final_registers.(kernel_save_r0)
      state ** frame).
  { sep_apply Hpack; entailer!. }
  exact (conj Hstate (conj Hvalue (conj Hexecution (Hframe after Howner)))).
Qed.

Lemma sem_pend_client_phase_uninterrupted_restore : forall phase environment local critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call mask saved acquired checkpoint cursor before written middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (sem_pend_client_phase_restore_input phase environment local critical sg call mask saved acquired checkpoint ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (sem_pend_client_phase_restore_output phase environment local critical sg call mask checkpoint ** frame) after.
Proof.
  intros phase environment local critical arch restore sg call mask saved acquired checkpoint cursor before written middle
    final_cursor after frame Hr0 Hmask Hinput Hprefix Hsuffix.
  assert (Hpure : interrupt_saved_value mask saved /\
      sem_pend_client_phase_restore_pre phase environment critical sg call mask checkpoint).
  { assert (Hobserve : sem_pend_client_phase_restore_input phase environment local critical sg call mask saved acquired
      checkpoint ** frame |-- coq_prop (interrupt_saved_value mask saved /\
        sem_pend_client_phase_restore_pre phase environment critical sg call mask checkpoint)).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exact Hfact. } exact (Hobserve before Hinput). }
  destruct Hpure as [Hsaved Hpre].
  assert (Hmasked : (sem_pend_fields_masked environment local critical sg call saved acquired checkpoint ** frame) before).
  { assert (Hforget : sem_pend_client_phase_restore_input phase environment local critical sg call mask saved acquired
      checkpoint ** frame |-- sem_pend_fields_masked environment local critical sg call saved acquired checkpoint ** frame).
    { intros heap [owned [rest [Hjoin [[Hfact Howner] Hframe]]]]; exists owned, rest; exact (conj Hjoin (conj Howner Hframe)). } exact (Hforget before Hinput). }
  destruct (kernel_continuation_call_uninterrupted_restore _ _ _ _ arch environment.(task_stack_call_continuations)
    restore kernel_program_fields_inv local sg (task_stack_call_active_key call) call saved acquired checkpoint
    cursor before written middle final_cursor after frame Hr0 Hmask Hmasked Hprefix Hsuffix)
    as [Hexecution [Hvalue Hclosed]].
  rewrite (proj2 Hsaved) in Hclosed.
  assert (Hsource : sem_pend_client_return_source environment critical sg call checkpoint call checkpoint)
    by apply sem_pend_client_return_source_refl.
  assert (Hphase : sem_pend_client_phase_restore_observation phase environment critical sg call checkpoint call checkpoint).
  { destruct phase; simpl in *; [contradiction|tauto|].
    destruct Hpre as [Hstage [Hidle Havailable]].
    exact (conj (kernel_call_normal_return_refl call checkpoint) (conj Hstage (conj Hidle Havailable))). }
  assert (Hpack : sem_pend_fields_closed environment local sg call mask checkpoint |--
    sem_pend_client_phase_restore_output phase environment local critical sg call mask checkpoint).
  { intros heap Howner; exists call, checkpoint; exact (conj (conj Hsource Hphase) Howner). }
  assert (Hframe : sem_pend_fields_closed environment local sg call mask checkpoint ** frame |--
    sem_pend_client_phase_restore_output phase environment local critical sg call mask checkpoint ** frame).
  { sep_apply Hpack; entailer!. }
  exact (conj Hexecution (conj Hvalue (Hframe after Hclosed))).
Qed.

Lemma sem_pend_client_phase_wait_restore_observation : forall environment critical sg original initial_mask initial
  observed eid timeout waiting call checkpoint returned current,
  sem_pend_client_phase_context sg call checkpoint ->
  sem_pend_client_phase_wait_at environment critical sg original initial_mask initial observed
    eid timeout waiting call checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  sem_pend_client_phase_restore_observation (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment critical sg call checkpoint returned current.
Proof.
  intros * Hcontext Hwait Hreturn.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  split; [exact Hafter|].
  eapply sem_pend_client_phase_wait_at_return;
    [exact Hwait|exact (proj1 Hcontext)|exact Hreturn|
     exact (proj1 (proj2 Hcontext))|exact (proj1 (proj2 Hafter))].
Qed.

Lemma sem_pend_client_phase_return_restore_observation : forall environment critical sg call mask checkpoint returned current,
  UCOS2_state_inv sg checkpoint ->
  sem_pend_client_phase_restore_pre SemPendReturnPhase environment critical sg call mask checkpoint ->
  sem_pend_client_return_source environment critical sg call checkpoint returned current ->
  os_sched_task_ready_source environment sg returned current ->
  sem_pend_client_phase_restore_observation SemPendReturnPhase environment critical sg call checkpoint returned current.
Proof.
  intros * Hvalid [Hstage [Hidle Havailable]] Hreturn Hready.
  eapply sem_pend_client_restore_from_ready_source;
    [apply kernel_call_normal_return_refl|exact Hreturn|exact Hvalid|exact Hstage|exact Hidle|exact Havailable|exact Hready].
Qed.

(** The first and second positive-count paths use the same literal count
    update. Their preceding source and guard observations remain at the
    actual checkpoint; no returned stage is an input here. *)
Lemma sem_pend_client_phase_immediate_restore_pre : forall environment critical sg call mask
  before eid event fields timeout checkpoint,
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  kernel_running_idle_ready sg before -> kernel_call_stack_available call before ->
  before.(EventState).(inUsedEventStates) eid = Some event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event.(semFields) = Some fields -> sem_pend_first_critical sg eid timeout before SemPendAcquired checkpoint ->
  UCOS2_state_inv sg checkpoint /\
  sem_pend_client_phase_restore_pre SemPendReturnPhase environment critical sg call mask checkpoint.
Proof.
  intros * Hvalid Hstage Hidle Havailable Hevent Htype Hfields Hstep.
  destruct (sem_pend_client_immediate_checkpoint sg call before eid event fields timeout checkpoint
    Hvalid Hstage Hidle Havailable Hevent Htype Hfields Hstep) as [Hvalid' [Hnormal Hpost]].
  exact (conj Hvalid' Hpost).
Qed.

Lemma sem_pend_client_phase_cleanup_restore_pre : forall environment critical sg call mask resumed eid
  old result checkpoint,
  sem_pend_resume_entry sg resumed eid call.(os_sched_call_stack).(stackLeaseSlot) old ->
  sem_pend_client_phase_context sg call resumed -> old.(curPrio) <> sg.(osLowestPrio) ->
  sem_pend_resume_critical sg eid resumed result checkpoint ->
  UCOS2_state_inv sg checkpoint /\
  sem_pend_client_phase_restore_pre SemPendReturnPhase environment critical sg call mask checkpoint.
Proof.
  intros * Hentry [Hvalid [Hsource [Hrunning [Hidle [Havailable Hcache]]]]] Hnonidle Hstep.
  destruct (sem_pend_client_cleanup_checkpoint sg call resumed eid old result checkpoint
    Hentry Hsource Hrunning Hnonidle Hcache Hidle Havailable Hstep) as [Hvalid' [Hnormal Hpost]].
  exact (conj Hvalid' Hpost).
Qed.

Lemma sem_pend_client_phase_wait_restore_pre : forall environment critical sg original returned mask saved
  before observed entry eid event tid old timeout,
  sem_pend_client_wait_origin environment critical sg original returned mask saved before observed
    entry eid event tid old ->
  entry.(SchedState).(isRunning) = true -> kernel_running_idle_ready sg entry ->
  kernel_call_stack_available original entry ->
  sem_pend_client_phase_restore_pre
    (SemPendWaitPhase original mask before observed eid timeout
      (event_pend_state sg entry eid event tid old PendSem timeout))
    environment critical sg original mask (event_pend_state sg entry eid event tid old PendSem timeout).
Proof.
  intros * Horigin Hrunning Hidle Havailable.
  pose proof (sem_pend_client_wait_origin_history environment critical sg original returned mask saved
    before observed entry eid event tid old timeout Horigin) as Hhistory.
  pose proof Hhistory as [Hvalid [Hsource [Hcache Hrest]]].
  pose proof Horigin as [_ [Hentry [Horigin_call Hentry_rest]]].
  pose proof Hentry as [_ [_ [_ [Hold [_ [_ [Hnonidle Hentry_tail]]]]]]].
  split; [reflexivity|]. split.
  - split; [exact Hvalid|]. split; [exact Hsource|]. split; [exact Hrunning|].
    split.
    + intros _; change (task_idle_ready sg
        (glob_task_set_usedtask entry.(TskState) tid
          (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)))).
      eapply task_update_non_idle_preserves_idle_ready; [exact Hold|exact Hnonidle|exact (Hidle Hrunning)].
    + split; [exact Havailable|exact Hcache].
  - eapply sem_pend_client_phase_wait_at_initial; [unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call; auto|exact Hhistory].
Qed.

(** Only the same annotated client prefix and this actual final action are
    joined. Private Timer cuts require no invented public Timer segment. *)
Lemma sem_pend_client_phase_return_last_step : forall environment critical sg original returned before
  origin transient acquired action
  (prefix : kernel_client_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin) before false origin transient),
  sem_pend_client_source_calls environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    original.(os_sched_call_origin) before false origin transient prefix ->
  critical.(critical_region_clients) action -> kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
  kernel_client_stops action original.(os_sched_call_invocation) = false ->
  kernel_client_step action sg transient acquired ->
  task_execution_source_step environment.(task_stack_call_external) environment.(task_stack_call_port)
    sg origin transient returned.(os_sched_call_origin) acquired ->
  tmr_task_source_call_receipt environment.(task_stack_call_external) action sg transient acquired ->
  kernel_call_normal_return original before returned acquired ->
  sem_pend_client_return_source environment critical sg original before returned acquired.
Proof.
  intros * Hprefix Hin Hforeign Hstop Hstep Hexecution Hreceipt Hnormal.
  assert (Hevent : forall invocation, (None : option nat) = Some invocation ->
      kernel_client_event_actor action <> Some invocation) by (intros; discriminate).
  pose proof (sem_pend_client_source_calls_single_step _ _ _ _ _ _ _ _ _ _ _
    Hin Hforeign Hevent Hstep Hexecution Hreceipt) as Hlast_segment.
  rewrite Hstop in Hlast_segment; destruct Hlast_segment as [last Hlast].
  destruct (sem_pend_client_source_calls_append _ _ _ _ _ _ _ _ _ _ _ prefix Hprefix
    _ _ _ last Hlast) as [joined Hjoined].
  eapply sem_pend_client_return_source_from_legacy; eassumption.
Qed.

(** The C cut keeps the actual first returned record. Only pure facts
    depending on its proved invocation/origin/stack fields are transported;
    no record equality or heap-owner replacement is asserted. *)
Lemma sem_pend_client_phase_wait_restore_returned_pre : forall environment critical sg original returned mask saved
  before observed entry eid event tid old timeout,
  sem_pend_client_wait_origin environment critical sg original returned mask saved before observed
    entry eid event tid old ->
  entry.(SchedState).(isRunning) = true -> kernel_running_idle_ready sg entry ->
  kernel_call_stack_available original entry ->
  sem_pend_client_phase_restore_pre
    (SemPendWaitPhase original mask before observed eid timeout
      (event_pend_state sg entry eid event tid old PendSem timeout))
    environment critical sg returned mask (event_pend_state sg entry eid event tid old PendSem timeout).
Proof.
  intros * Horigin Hrunning Hidle Havailable.
  pose proof (sem_pend_client_phase_wait_restore_pre environment critical sg original returned mask saved
    before observed entry eid event tid old timeout Horigin Hrunning Hidle Havailable) as Hpre.
  pose proof (proj1 (proj2 (proj1 Horigin))) as Hsame.
  destruct Hpre as [Hmask [[Hvalid [Hsource [Hrunning' [Hidle' [Havailable' Hcache]]]]] Hwait]].
  split; [exact Hmask|]. split.
  - split; [exact Hvalid|]. split.
    + apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original _ Hsame)); exact Hsource.
    + split; [exact Hrunning'|]. split; [exact Hidle'|]. split; [|exact Hcache].
      unfold kernel_call_stack_available; rewrite (proj1 (proj2 Hsame)); exact Havailable'.
  - destruct Hwait as [_ Hrest]; exact (conj Hsame Hrest).
Qed.

Lemma sem_pend_client_phase_return_output : forall environment local critical sg call mask checkpoint,
  sem_pend_client_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint |--
  sem_pend_client_fields_restore_output environment local critical sg call mask checkpoint.
Proof.
  intros environment local critical sg call mask checkpoint heap [returned [current [[Hsource Hphase] Howner]]].
  exists returned, current; split; assumption.
Qed.

Lemma sem_pend_client_phase_return_same_postcondition : forall environment local critical sg context call mask
  pevent timeout perr before checkpoint error X,
  sem_pend_client_checkpoint_result environment critical sg context pevent timeout before error checkpoint ->
  kernel_stack_call_same_call call context ->
  sem_pend_client_fields_call_safe environment critical sg context pevent timeout before X ->
  TT ** sem_pend_client_phase_restore_output SemPendReturnPhase environment local critical sg call mask checkpoint **
    perr # UChar |-> error |--
  sem_pend_client_fields_call_post environment critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hcheckpoint Hsame Hsafe.
  sep_apply (sem_pend_client_phase_return_output environment local critical sg call mask checkpoint).
  sep_apply (sem_pend_client_fields_call_post_from_restore environment local critical sg context call mask
    pevent timeout perr before checkpoint error X Hcheckpoint Hsame Hsafe); entailer!.
Qed.

(** This composition begins at the actual IRQ take, with handler authority,
    the selected dormant descriptor and its fields world. The take's exact
    stack/SP/fragments link that descriptor to the same transfer. Restore and
    the Save suffix create the masked owner; it is not a premise.

    The annotated prefix and actual action receipt still belong to the real
    interpreter. The actual normal-return/rely obligations are independent.
    No source packet is recovered from a desired phase or endpoint fact. *)
Lemma sem_pend_client_phase_irq_restored_save :
  forall phase environment local critical arch
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original mask before origin irq_entry handler transfer action
    (prefix : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before false origin irq_entry)
    selected registers heap restored final_registers final_state after (frame : Assertion),
  let acquired := os_int_exit_installed_state transfer in
  let returned := armv7a_continuation_resumed_call selected original in
  sem_pend_client_source_calls environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false origin irq_entry prefix ->
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
  kernel_client_stops action original.(os_sched_call_invocation) = false ->
  kernel_client_step action sg irq_entry acquired ->
  tmr_task_source_call_receipt environment.(task_stack_call_external) action sg irq_entry acquired ->
  os_int_exit_transfer_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    sg handler irq_entry transfer ->
  selected.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) ->
  selected.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
  selected.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) ->
  selected.(armv7a_continuation_call) = Some original ->
  original.(os_sched_call_origin) = RunningInvocation
    transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
    transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) ->
  selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
  interrupt_saved_value mask registers.(kernel_save_r0) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  armv7a_continuation_restore_reads selected heap ->
  (interrupt_platform_running environment.(task_stack_call_platform)
     handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
   os_int_exit_context_resources environment.(task_stack_call_port) handler **
   task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
     selected.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation environment.(task_stack_call_continuations) selected **
   (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      local sg (task_stack_call_active_key returned) acquired ** frame)) heap ->
  armv7a_restore_transition environment.(task_stack_call_continuations) handler selected heap restored ->
  armv7a_save_suffix_transition suffix registers acquired restored final_registers final_state after ->
  sem_pend_client_phase_save_pre phase environment critical sg original mask before ->
  kernel_call_normal_return original before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  final_state = acquired /\ after.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
  final_registers.(kernel_save_return_word) = Some selected.(armv7a_continuation_lr) /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  (sem_pend_client_phase_save_output phase environment local critical sg original mask
     final_registers.(kernel_save_r0) before **
   (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) after.
Proof.
  intros phase environment local critical arch suffix sg original mask before origin irq_entry handler
    transfer action prefix selected registers heap restored final_registers final_state after frame
    acquired returned Hprefix Hin Hforeign Hstop Hstep Hreceipt Htransfer
    Hlease Hsp Hfragments Hcall Horigin Hcursor Hcpsr Hr0 Hlr Hsaved Hrestored_saved Hreads Hpre
    Hrestore Hsuffix Hphase_pre Hnormal Hrely.
  destruct (sem_pend_fields_irq_restored_save_resources environment local critical arch suffix sg handler
    selected original acquired registers heap restored final_registers final_state after frame
    Hcall Hcursor Hcpsr Hr0 Hlr Hrestored_saved Hreads Hpre Hrestore Hsuffix)
    as [Hstate [Hmemory [Hreturn [Hvalue Howner]]]].
  pose proof (proj2 (proj1 Hreads)) as Hselected_stack.
  rewrite Hcall in Hselected_stack.
  assert (Hi : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation)) by reflexivity.
  assert (Ho : returned.(os_sched_call_origin) = original.(os_sched_call_origin)) by reflexivity.
  assert (Hstack : returned.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { change (selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
    symmetry; exact Hselected_stack. }
  assert (Hreturned : returned.(os_sched_call_origin) = RunningInvocation
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
      transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration)).
  { exact Horigin. }
  assert (Hexecution : task_execution_source_step environment.(task_stack_call_external)
      environment.(task_stack_call_port) sg origin irq_entry returned.(os_sched_call_origin) acquired).
  { rewrite Hreturned; eapply TaskExecutionInterruptTransfer; exact Htransfer. }
  pose proof (sem_pend_client_phase_return_last_step environment critical sg original returned before
    origin irq_entry acquired action prefix Hprefix Hin Hforeign Hstop Hstep Hexecution Hreceipt Hnormal) as Hsource.
  pose proof (sem_pend_client_phase_save_output_intro phase environment local critical sg
    original returned mask registers.(kernel_save_r0) before acquired Hphase_pre Hsource Hsaved Hrely) as Hphase.
  rewrite Hstate, Hvalue in Howner.
  assert (Hframe : sem_pend_fields_masked environment local critical sg returned
      registers.(kernel_save_r0) acquired acquired **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame) |--
    sem_pend_client_phase_save_output phase environment local critical sg original mask
      registers.(kernel_save_r0) before **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame)).
  { sep_apply Hphase; entailer!. }
  split; [exact Hstate|]. split; [exact Hmemory|]. split; [exact Hreturn|].
  split; [exact Hvalue|]. rewrite Hvalue; exact (Hframe after Howner).
Qed.

(** The actual install producer selects installed/selected once. Its actual
    restore continuation is then consumed with the same descriptor, registers
    and suffix. Source construction uses that selected resumed call and the
    same saved-stack/destination binding. The selected local resource remains
    framed beside the phase output and the unchanged caller frame. *)
Lemma sem_pend_client_phase_task_installed_save :
  forall phase environment local critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original mask before context outgoing hooked incoming resumed action
    (prefix : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before false context.(os_sched_call_origin) hooked)
    heap (frame : Assertion),
  let resource := kernel_saved_continuation_entry environment.(task_stack_call_continuations)
    hooked.(TskState) local in
  let acquired := os_sched_install_context context outgoing incoming hooked in
  sem_pend_client_source_calls environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false context.(os_sched_call_origin) hooked prefix ->
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
  kernel_client_stops action original.(os_sched_call_invocation) = false ->
  kernel_client_step action sg hooked acquired ->
  tmr_task_source_call_receipt environment.(task_stack_call_external) action sg hooked acquired ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) heap ->
  sem_pend_client_phase_save_pre phase environment critical sg original mask before ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at acquired incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage acquired.(TskState) (Some (task_stack_key incoming)) /\
    (forall registers restored final_registers final_state after,
      selected.(armv7a_continuation_call) = Some original ->
      original.(os_sched_call_origin) = RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
      selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      interrupt_saved_value mask registers.(kernel_save_r0) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_task_restore_transition task_abi context selected installed restored ->
      armv7a_save_suffix_transition suffix registers acquired restored final_registers final_state after ->
      kernel_call_normal_return original before (armv7a_continuation_resumed_call selected original) acquired ->
      sem_pend_save_rely sg before acquired ->
      armv7a_task_restored_source environment.(task_stack_call_external) selected /\
      final_state = acquired /\ after.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      final_registers.(kernel_save_return_word) = Some selected.(armv7a_continuation_lr) /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
      (sem_pend_client_phase_save_output phase environment local critical sg original mask
         final_registers.(kernel_save_r0) before ** (local selected ** frame)) after).
Proof.
  intros phase environment local critical arch task_abi suffix sg original mask before context outgoing
    hooked incoming resumed action prefix heap frame resource acquired Hprefix Hin Hforeign Hstop
    Hstep Hreceipt Hsaved_stack Hdestination Haddress Hcoverage Hpre Hphase_pre.
  destruct (sem_pend_fields_task_installed_save_resources environment local critical arch task_abi suffix
    sg context outgoing hooked incoming resumed heap frame Hsaved_stack Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments
      [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold acquired in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hbinding|]. split; [exact Hlease|]. split; [exact Hfragments|].
  split; [exact Hcurrent|]. split; [exact Hcovered|].
  intros registers restored final_registers final_state after Hcall Horigin Hcursor Hcpsr Hr0 Hlr
    Hsaved Hrestored_saved Hactual Hsuffix Hnormal Hrely.
  destruct (Hrestore original registers restored final_registers final_state after Hcall Horigin
    Hcursor Hcpsr Hr0 Hlr Hrestored_saved Hactual Hsuffix)
    as [Hsource [Hstate [Hmemory [Hreturn [Hvalue Howner]]]]].
  pose (returned := armv7a_continuation_resumed_call selected original).
  pose proof (proj2 Hbinding) as Hselected_stack.
  rewrite Hcall in Hselected_stack.
  assert (Hi : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation)) by reflexivity.
  assert (Ho : returned.(os_sched_call_origin) = original.(os_sched_call_origin)) by reflexivity.
  assert (Hstack : returned.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { change (selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
    symmetry; exact Hselected_stack. }
  assert (Hreturned : returned.(os_sched_call_origin) = RunningInvocation
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)).
  { exact Horigin. }
  assert (Hexecution : task_execution_source_step environment.(task_stack_call_external)
      environment.(task_stack_call_port) sg context.(os_sched_call_origin) hooked returned.(os_sched_call_origin) acquired).
  { rewrite Hreturned; eapply TaskExecutionSchedulerInstall; eassumption. }
  pose proof (sem_pend_client_phase_return_last_step environment critical sg original returned before
    context.(os_sched_call_origin) hooked acquired action prefix Hprefix Hin Hforeign Hstop Hstep
    Hexecution Hreceipt Hnormal) as Hreturn_source.
  pose proof (sem_pend_client_phase_save_output_intro phase environment local critical sg
    original returned mask registers.(kernel_save_r0) before acquired Hphase_pre Hreturn_source Hsaved Hrely) as Hphase.
  rewrite Hstate, Hvalue in Howner.
  assert (Hframe : sem_pend_fields_masked environment local critical sg returned
      registers.(kernel_save_r0) acquired acquired ** (local selected ** frame) |--
    sem_pend_client_phase_save_output phase environment local critical sg original mask
      registers.(kernel_save_r0) before ** (local selected ** frame)).
  { sep_apply Hphase; entailer!. }
  split; [exact Hsource|]. split; [exact Hstate|]. split; [exact Hmemory|].
  split; [exact Hreturn|]. split; [exact Hvalue|].
  rewrite Hvalue; exact (Hframe after Howner).
Qed.

