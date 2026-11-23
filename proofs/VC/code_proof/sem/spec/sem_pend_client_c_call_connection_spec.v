Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_sequence_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_typed_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_receipt_producer_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import SemPendEventReadySource.
Import SelectedEnvironmentCProgram SelectedEnvironmentScopedEnvironment.
Import SelectedEnvironmentPhaseEffects SelectedEnvironmentPhaseProperties.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The private packet uses the existing indexed step receipt and the
    observation of this same call.  It introduces no new source union. *)
Definition sem_pend_client_program_call_observation environment critical sg observer origin
  state before input stopped current after output
  (step : kernel_program_c_step environment critical sg observer origin
    state before input stopped current after output) first last : Prop :=
  sem_pend_program_c_step_receipt environment critical sg observer origin
    _ _ _ _ _ _ _ step /\
  sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
    first state stopped last current.

Lemma sem_pend_client_program_call_observation_trace :
  forall environment critical sg observer origin state before input stopped current after output step first last,
  sem_pend_client_program_call_observation environment critical sg observer origin
    state before input stopped current after output step first last ->
  sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
    first state stopped last current.
Proof. intros until last; intros [_ Htrace]; exact Htrace. Qed.

(** The actor and membership belong to this actual module call.  The helper
    arguments, receipt and source are obtained from its real pre/post pair. *)
Lemma sem_pend_event_ready_c_call_certificate :
  forall environment critical sg observer stored_origin origin actor entry eid event slot old kind message result returned
    frame before after,
  critical.(critical_region_clients) (event_task_rdy_source_client actor eid kind message result) ->
  actor <> Some observer ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  sem_pend_source_state_facts sg entry ->
  event_type_to_pend_type event.(eventType) = Some kind -> result <> PendTimeout ->
  (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** frame) before ->
  (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** frame) after ->
  exists segment : WakeComponent.kernel_wake_c_segment sg entry before
      (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** frame)
      (event_wake_state sg entry eid event slot old kind message result) after
      (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** frame),
    let step := @KernelProgramCWake environment critical sg observer stored_origin _ _ _ _ _ _ segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_c_sequence_call_certificate _
      (sem_pend_client_program_call_observation environment critical sg observer stored_origin)
      _ _ _ _ _ _ _ run origin origin /\
    (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** frame) after.
Proof.
  intros environment critical sg observer stored_origin origin actor entry eid event slot old kind message result
    returned frame before after Hmember Hforeign Hlookup Hfacts Hkind Hresult Hpre Hpost.
  destruct (sem_pend_event_ready_typed_step environment critical sg observer stored_origin entry eid event slot old
    kind message result returned frame before after Hlookup Hfacts Hkind Hresult Hpre Hpost)
    as [segment [Hreceipt Howned]].
  pose proof (proj2 (tmr_task_event_ready_c_post_receipt environment.(task_stack_call_external) actor sg
    entry eid event slot old kind message result returned frame before after Hlookup Hkind Hresult Hpre Hpost))
    as Hcall.
  pose proof (tmr_task_source_call_receipt_step _ _ _ _ _ Hcall) as Hstep.
  assert (Htrace : sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
    origin entry false origin (event_wake_state sg entry eid event slot old kind message result)).
  { change false with (kernel_client_stops (event_task_rdy_source_client actor eid kind message result) observer).
    eapply sem_pend_registered_framed_call_observed_source.
    - exact Hmember.
    - exact Hforeign.
    - intros; discriminate.
    - exact Hstep.
    - unfold event_wake_state, sched_wake_by_status.
      destruct (task_status_is_suspended
        (encode_task_status (task_event_wake_single old kind message result).(stat))); reflexivity.
    - exact Hcall. }
  exists segment; cbn zeta; split; [|exact Howned].
  apply SemPendCSequenceCallAtom.
  exact (conj Hreceipt Htrace).
Qed.

(** This is the existing concrete SemPost Extra supplier.  Open its single
    result once and retain Hstep/Hmiddle together with its same-index receipt;
    no opaque Henv or unrelated trace is reconstructed. *)
Lemma sem_pend_sem_post_module_call_output :
  forall environment critical local sg observer origin request entry node result before after (frame : Assertion),
  critical.(critical_region_clients)
    (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event)) ->
  request.(sem_pend_fields_post_actor) <> observer ->
  sem_post_lookup entry request.(sem_pend_fields_post_event) node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg request.(sem_pend_fields_post_event) ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg request.(sem_pend_fields_post_event)) result before after ->
  kernel_client_heap_step sem_pend_fields_post_heap_execution sg
    (KernelClientHeapExtra request) before KernelClientHeapClosed after /\
  exists current,
    kernel_client_heap_state_step sem_pend_fields_post_heap_effect sg
      (KernelClientHeapExtra request) entry KernelClientHeapClosed current /\
    (exists priority, sem_post_wake_result sg request.(sem_pend_fields_post_event) entry current priority) /\
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg observer None origin entry false origin current /\
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg current ** frame) after.
Proof.
  intros environment critical local sg observer origin request entry node result before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  destruct (sem_pend_fields_post_registered_resources environment critical local sg observer origin request entry node
    result before after frame Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual)
    as [Hheap [current [Hstep [Hwake [[trace Hcalls] Hmiddle]]]]].
  split; [exact Hheap|]. exists current; split; [exact Hstep|].
  split; [exact Hwake|]. split; [|exact Hmiddle].
  eapply SemPendObservedLegacy with (trace := trace).
  eapply sem_pend_client_source_local_receipt_calls; exact Hcalls.
Qed.

(** Actual completed macros already own the endpoint packet.  Only the
    observation of their actual module calls is added; ABI execution is not
    reconstructed and no future owner or ready fact is assumed. *)
Lemma sem_pend_completed_save_call_output :
  forall environment critical local next_local active sg call mask before first_heap saved returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    call mask before first_heap saved false returned current last_heap ->
  sem_pend_client_phase_context sg call before ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) current ->
  ((coq_prop (sem_pend_client_return_source environment critical sg call before returned current /\
      kernel_call_control_rely sg before current /\ interrupt_saved_value mask saved /\
      sem_pend_save_rely sg before current) &&
    sem_pend_fields_masked environment next_local critical sg returned saved current current) **
    active returned current) last_heap.
Proof.
  intros environment critical local next_local active sg call mask before first_heap saved returned current last_heap
    Hactual Hcontext Htrace.
  destruct (sem_pend_actual_save_control environment critical local next_local active sg call mask
    before first_heap saved false returned current last_heap Hactual (proj1 (proj2 Hcontext)))
    as [Hnormal [Hcontrol [Henabled Howner]]].
  pose proof (proj1 (os_sched_continuation_c_save_execution_sequence_source environment critical local next_local active
    sg call mask before first_heap saved false returned current last_heap Hactual)) as Hsaved.
  assert (Hreturn : sem_pend_client_return_source environment critical sg call before returned current)
    by exact (conj Htrace Hnormal).
  pose proof (proj1 (proj2 (os_sched_continuation_c_save_execution_resources environment critical local next_local active
    sg call mask before first_heap saved false returned current last_heap Hactual))) as Hendpoint.
  pose proof (sem_pend_client_endpoint_save_rely _ _ _ _ _ _ _ Hcontext Hreturn Hendpoint) as Hrely.
  destruct (sem_pend_task_caller_masked _ _ _ _ _ _ _ _ _ last_heap Howner)
    as [owned [rest [Hjoin [Hmasked Hactive]]]].
  exists owned, rest; exact (conj Hjoin (conj (conj (conj Hreturn (conj Hcontrol (conj Hsaved Hrely))) Hmasked) Hactive)).
Qed.

Lemma sem_pend_completed_save_phase_output :
  forall phase environment critical local next_local active sg call mask before first_heap saved returned current last_heap,
  os_sched_continuation_c_save_execution environment critical local next_local active sg
    call mask before first_heap saved false returned current last_heap ->
  sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) current ->
  (sem_pend_clear_status_phase_save_output phase environment next_local critical sg call mask saved before **
    active returned current) last_heap.
Proof.
  intros until last_heap; intros Hactual Hpre Htrace.
  eapply sem_pend_client_saved_phase_output; [exact Hpre|].
  eapply sem_pend_completed_save_call_output; [exact Hactual|exact (proj1 Hpre)|exact Htrace].
Qed.

Lemma sem_pend_completed_restore_call_output :
  forall environment critical local next_local active sg call saved acquired before first_heap returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap ->
  kernel_call_task_source call before ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) current ->
  sem_pend_client_return_source environment critical sg call before returned current /\
  kernel_call_control_rely sg before current /\
  flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller call) call before returned current /\
  (sem_pend_fields_closed environment next_local sg returned (armv7a_irq_fiq_mask saved) current **
    active returned current) last_heap.
Proof.
  intros until last_heap; intros Hactual Htask Htrace.
  destruct (proj2 (os_sched_continuation_c_restore_execution_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual))
    as [Hendpoint Howner].
  destruct (sem_pend_task_endpoint_control environment sg call before returned current Htask Hendpoint)
    as [Hnormal Hcontrol].
  split; [exact (conj Htrace Hnormal)|]. split; [exact Hcontrol|]. split; [exact Hendpoint|].
  exact (sem_pend_task_caller_closed _ _ _ _ _ _ _ _ last_heap Howner).
Qed.

Lemma sem_pend_completed_waiting_restore_sched_input :
  forall environment critical local next_local active sg original mask initial observed eid timeout waiting
    call saved acquired before first_heap returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap ->
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call before ->
  interrupt_saved_value mask saved ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) current ->
  ((coq_prop (sem_pend_client_return_source environment critical sg call before returned current /\
      kernel_call_control_rely sg before current) &&
    sem_pend_client_sched_input environment next_local critical sg original mask initial observed eid timeout
      waiting returned current) ** active returned current) last_heap.
Proof.
  intros until last_heap; intros Hactual [Hcontext [Hwait [Henabled Hfields]]] Hsaved Htrace.
  destruct (sem_pend_completed_restore_call_output _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual
    (proj1 (proj2 Hcontext)) Htrace) as [Hreturn [Hcontrol [Hendpoint Howner]]].
  rewrite (proj2 Hsaved) in Howner.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  assert (Hentry : sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout
    waiting returned current).
  { split; [exact Hafter|]. split.
    - eapply sem_pend_clear_status_phase_wait_at_return;
        [exact Hwait|exact (proj1 Hcontext)|exact Hreturn|
         exact (proj1 (proj2 Hcontext))|exact (proj1 (proj2 Hafter))].
    - split; [eapply sem_pend_control_selection_enabled; eassumption|].
      eapply sem_pend_sched_client_return_caller_fields;
        [exact Hreturn|exact (proj1 Hcontext)|exact (proj1 (proj2 (proj2 Hcontext)))|
         exact (proj1 (proj2 Hcontext))|exact (proj1 Hwait)|exact Hfields]. }
  destruct Howner as [owned [rest [Hjoin [Hclosed Hactive]]]].
  exists owned, rest; exact (conj Hjoin (conj (conj (conj Hreturn Hcontrol) (conj Hentry Hclosed)) Hactive)).
Qed.

Lemma sem_pend_completed_final_restore_save_input :
  forall environment critical local next_local active sg original mask initial observed eid timeout waiting
    call saved acquired released first_heap returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    call saved acquired released first_heap false returned current last_heap ->
  sem_pend_client_phase_context sg call released ->
  sem_pend_clear_status_phase_selected_at environment critical sg original mask initial observed eid timeout
    waiting call released ->
  sem_pend_client_sched_caller_fields sg original released -> interrupt_saved_value mask saved ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current ->
  ((coq_prop (sem_pend_client_return_source environment critical sg call released returned current /\
      kernel_call_control_rely sg released current /\ sem_pend_client_sched_caller_fields sg original current) &&
    sem_pend_clear_status_phase_save_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment next_local critical sg returned mask current) ** active returned current) last_heap.
Proof.
  intros until last_heap; intros Hactual Hcontext Hselected Hfields Hsaved Htrace.
  pose proof Hselected as [Hwait Hresume].
  destruct (sem_pend_completed_restore_call_output _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual
    (proj1 (proj2 Hcontext)) Htrace) as [Hreturn [Hcontrol [Hendpoint Howner]]].
  rewrite (proj2 Hsaved) in Howner.
  pose proof (sem_pend_client_phase_context_return _ _ _ _ _ _ _ Hreturn Hcontext) as Hafter.
  pose proof (sem_pend_clear_status_phase_wait_at_return _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hwait (proj1 Hcontext) Hreturn (proj1 (proj2 Hcontext)) (proj1 (proj2 Hafter))) as Hwait'.
  pose proof (sem_pend_selected_current_ready _ _ _ _ _ _ _ _ _ _ _ _ Hcontext Hselected) as Hready_before.
  pose proof (proj1 Hendpoint (conj (proj1 (proj2 Hcontext)) Hready_before)) as Hready_after.
  assert (Hmember : In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList)).
  { destruct Hready_after as [node [[Hnode [Hcur [Hpriority [Hmember Heffective]]]] Hgen]].
    rewrite <- (proj2 (proj2 (proj1 Hwait'))); exact Hmember. }
  pose proof (sem_pend_clear_status_phase_selected_from_member _ _ _ _ _ _ _ _ _ _ _ _ Hwait' Hafter Hmember)
    as Hselected'.
  assert (Hpre : sem_pend_clear_status_phase_save_pre
    (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment critical sg returned mask current).
  { exact (conj Hafter (conj eq_refl Hselected')). }
  assert (Hfields' : sem_pend_client_sched_caller_fields sg original current).
  { eapply sem_pend_sched_client_return_caller_fields;
      [exact Hreturn|exact (proj1 Hcontext)|exact (proj1 (proj2 (proj2 Hcontext)))|
         exact (proj1 (proj2 Hcontext))|exact (proj1 Hwait)|exact Hfields]. }
  destruct Howner as [owned [rest [Hjoin [Hclosed Hactive]]]].
  exists owned, rest; exact (conj Hjoin (conj (conj (conj Hreturn (conj Hcontrol Hfields')) (conj Hpre Hclosed)) Hactive)).
Qed.

Lemma sem_pend_completed_restore_phase_output :
  forall phase environment critical local next_local active sg call mask saved acquired before first_heap returned current last_heap,
  os_sched_continuation_c_restore_execution environment critical local next_local active sg
    call saved acquired before first_heap false returned current last_heap ->
  sem_pend_client_phase_context sg call before ->
  sem_pend_clear_status_phase_restore_pre phase environment critical sg call mask before ->
  interrupt_saved_value mask saved ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) current ->
  (sem_pend_clear_status_phase_restore_output phase environment next_local critical sg call mask before **
    active returned current) last_heap.
Proof.
  intros until last_heap; intros Hactual Hcontext Hpre Hsaved Htrace.
  destruct (sem_pend_completed_restore_call_output _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hactual
    (proj1 (proj2 Hcontext)) Htrace) as [Hreturn [Hcontrol [Hendpoint Howner]]].
  rewrite (proj2 Hsaved) in Howner.
  assert (Hphase : sem_pend_clear_status_phase_restore_observation phase environment critical sg call before returned current).
  { destruct phase.
    - contradiction.
    - destruct Hpre as [_ [Hcontext' Hwait]].
      eapply sem_pend_clear_status_phase_wait_restore_observation; eassumption.
    - eapply sem_pend_clear_status_phase_return_restore_observation; eassumption. }
  destruct Howner as [owned [rest [Hjoin [Hclosed Hactive]]]].
  exists owned, rest; split; [exact Hjoin|]. split; [|exact Hactive].
  exists returned, current; exact (conj (conj Hreturn Hphase) Hclosed).
Qed.

(** These two call-site compositions start with the same indexed run/certificate
    used by C23 and finish at the ordinary CPU phase post. Their output is not
    obtained by choosing a second endpoint-equal run. *)
Lemma sem_pend_c_call_save_phase_output :
  forall phase environment critical local next_local active sg mask call before first_heap private_input private_output private_before whole_before returned current environment_heap arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    registers final_registers whole_after
    (leaf : forall state heap input stopped result output_heap output,
      kernel_program_environment_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop)
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      call mask before whole_before private_input false returned current environment_heap private_output),
  (forall state heap input stopped result output_heap output step first last,
    leaf state heap input stopped result output_heap output step first last ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg call.(os_sched_call_invocation) None
      first state stopped last result) ->
  sem_pend_clear_status_phase_save_pre phase environment critical sg call mask before ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    call mask before whole_before private_input false returned current environment_heap private_output run ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin))
    leaf
    _ _ _ _ _ _ _ run call.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  flag_pend_caller_save_input environment critical local active sg (FlagPendTaskCaller call) call mask before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists last_heap (actual : os_sched_continuation_c_save_execution environment critical local next_local active sg
    call mask before first_heap final_registers.(kernel_save_r0) false returned current last_heap),
  (sem_pend_clear_status_phase_save_output phase environment next_local critical sg call mask
    final_registers.(kernel_save_r0) before ** active returned current) last_heap.
Proof.
  intros phase environment critical local next_local active sg mask call before first_heap private_input private_output
    private_before whole_before returned current environment_heap arch save registers final_registers whole_after leaf run
    Hdecode Hpre Hsource Hcalls Hinput Hprivate Hjoin Hword Hvalid Hmask Hsuffix.
  destruct (sem_pend_c_sequence_save_output environment critical local next_local active sg mask call before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch save registers
    final_registers whole_after leaf run Hdecode (proj1 Hpre) Hsource Hcalls Hinput Hprivate Hjoin Hword Hvalid Hmask Hsuffix)
    as [last_heap [actual Houtput]].
  exists last_heap, actual.
  eapply sem_pend_client_saved_phase_output; [exact Hpre|exact Houtput].
Qed.

Lemma sem_pend_c_call_restore_phase_output :
  forall phase mask environment critical local next_local active sg original saved acquired before first_heap
    private_input private_output private_before whole_before returned current environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after
    (leaf : forall state heap input stopped result output_heap output,
      kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
        state heap input stopped result output_heap output -> TaskInvocationOrigin -> TaskInvocationOrigin -> Prop)
    (run : flag_pend_scoped_environment_run environment critical local next_local active sg
      original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
      false returned current environment_heap private_output),
  (forall state heap input stopped result output_heap output step first last,
    leaf state heap input stopped result output_heap output step first last ->
    sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
      first state stopped last result) ->
  sem_pend_client_phase_context sg original before ->
  sem_pend_clear_status_phase_restore_pre phase environment critical sg original mask before ->
  interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local active sg
    (FlagPendTaskCaller original) original saved acquired before first_heap ->
  private_input private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  flag_pend_scoped_environment_source environment critical local next_local active sg None
    original (armv7a_irq_fiq_mask saved) before prefix_heap private_input
    false returned current environment_heap private_output run ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  sem_pend_c_sequence_call_certificate
    (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin))
    leaf _ _ _ _ _ _ _ run original.(os_sched_call_origin) returned.(os_sched_call_origin) ->
  exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local next_local active sg
    original saved acquired before first_heap false returned current last_heap),
  (sem_pend_clear_status_phase_restore_output phase environment next_local critical sg original mask before **
    active returned current) last_heap.
Proof.
  intros phase mask environment critical local next_local active sg original saved acquired before first_heap private_input
    private_output private_before whole_before returned current environment_heap arch restore cursor written prefix_heap
    final_cursor whole_after leaf run Hdecode Hcontext Hpre Hsaved Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hsource Hsuffix Hcalls.
  destruct (sem_pend_c_sequence_restore_output environment critical local next_local active sg original saved acquired
    before first_heap private_input private_output private_before whole_before returned current environment_heap arch restore
    cursor written prefix_heap final_cursor whole_after leaf run Hdecode (proj1 (proj2 Hcontext)) Hr0 Hmask Hinput Hprivate
    Hjoin Hprefix Hsource Hsuffix Hcalls) as [last_heap [actual Houtput]].
  destruct Houtput as [owned [rest [Hjoin_after [[[Hreturn Hfacts] Hclosed] Hactive]]]].
  exists last_heap, actual.
  eapply sem_pend_completed_restore_phase_output;
    [exact actual|exact Hcontext|exact Hpre|exact Hsaved|exact (proj1 Hreturn)].
Qed.
