Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_completed_family_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_waiting_recovery_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_acquired_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selected_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_idle_frames_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_wake_status_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_idle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_value_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_completion_composition_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_next_completion_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_wrapper_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_outer_completion_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_waiting_environment_consumer_spec.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_waiting_receipt_output_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations FlagPendSchedulerResources.
Import PrimitiveComponent PendPhaseCandidate CriticalComponent SelectedCProgram SelectedCSource.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingReceiptReindex FlagWaitingNodeInclusion.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Import PrimitiveComponent PendPhaseCandidate CriticalComponent SelectedCProgram SelectedCSource.
Import FlagWaitingRecovery FlagWaitingSuccessor FlagWaitingReceiptReindex FlagWaitingNodeInclusion.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagWaitingPublishedReturn.

(** This recovery starts at the post of the actual wake.  Its source is
    that wake's registration/result and the continuation from the same
    publication heap.  The old linked receipt is never reinterpreted as
    the private node owner. *)
Lemma flag_waiting_published_receipt_current :
  forall environment critical sg observer origin entry reference call pointer bits result schedule post
    published input stopped current after output returned,
  flag_active_waiting_registration reference pointer call entry ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) ->
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    post published input stopped current after output ->
  task_tcb_init_stack_same_call returned reference ->
  kernel_call_task_source returned current ->
  flag_pend_waiting_receipt sg reference pointer call post |--
    flag_pend_waiting_receipt sg reference pointer returned current.
Proof.
  intros environment critical sg observer origin entry reference call pointer bits result schedule post
    published input stopped current after output returned Hregistration Hresult Hstep Hrun Hsame Hreturned.
  destruct (flag_active_task_rdy_waiting_registration sg entry reference call pointer bits result schedule post
    Hregistration Hstep) as [_ Hnone].
  assert (Hcurrent_none : current.(FlagState).(flagWaitNodes) pointer = None).
  { eapply flag_wait_nodes_included_absent;
      [eapply kernel_program_selected_c_sequence_nodes_included; exact Hrun|exact Hnone]. }
  eapply flag_pend_detached_receipt_current; try eassumption.
  eapply flag_task_rdy_selected_sequence_detached_fields; eassumption.
Qed.

Lemma flag_waiting_published_receipt_active :
  forall environment critical sg observer origin entry reference call pointer bits result schedule post
    published input stopped current after output returned,
  flag_active_waiting_registration reference pointer call entry ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) ->
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    post published input stopped current after output ->
  task_tcb_init_stack_same_call returned reference ->
  kernel_call_task_source returned current ->
  task_idle_ready sg current.(TskState) ->
  flag_pend_non_idle_at sg reference current ->
  flag_pend_waiting_receipt sg reference pointer call post |--
    flag_pend_wait_active sg reference pointer returned current.
Proof.
  intros environment critical sg observer origin entry reference call pointer bits result schedule post
    published input stopped current after output returned Hregistration Hresult Hstep Hrun
    Hsame Hreturned Hidle Hnonidle.
  sep_apply_l_atomic (flag_waiting_published_receipt_current environment critical sg observer origin
    entry reference call pointer bits result schedule post published input stopped current after output returned
    Hregistration Hresult Hstep Hrun Hsame Hreturned).
  unfold flag_pend_waiting_receipt, flag_pend_wait_active; entailer!.
Qed.

(** A real suffix returns the fixed receipt published at post.  This lemma
    replaces only its interpretation in that very output heap.  packet
    preserves the outer call's observations, so the API before-state is
    not reset to post. *)
Lemma flag_waiting_published_restore_owner :
  forall environment critical sg observer origin entry reference call pointer bits result schedule post
    published input stopped current after returned next_local frame saved acquired (packet : Prop)
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      post published input stopped current after
      (coq_prop packet && flag_pend_caller_restore_input environment critical next_local
        (fun _ _ => flag_pend_waiting_receipt sg reference pointer call post ** frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current)),
  flag_active_waiting_registration reference pointer call entry ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) ->
  task_tcb_init_stack_same_call returned reference ->
  kernel_call_task_source returned current ->
  task_idle_ready sg current.(TskState) ->
  flag_pend_non_idle_at sg reference current ->
  (coq_prop packet && flag_pend_caller_restore_input environment critical next_local
    (fun returned current => flag_pend_wait_active sg reference pointer returned current ** frame) sg
    (FlagPendTaskCaller returned) returned saved acquired current) after.
Proof.
  intros environment critical sg observer origin entry reference call pointer bits result schedule post
    published input stopped current after returned next_local frame saved acquired packet run
    Hregistration Hresult Hstep Hsame Hreturned Hidle Hnonidle.
  pose proof (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)) as Houtput.
  pose proof (flag_waiting_published_receipt_active environment critical sg observer origin
    entry reference call pointer bits result schedule post published input stopped current after _ returned
    Hregistration Hresult Hstep run Hsame Hreturned Hidle Hnonidle) as Hrecover.
  match type of Houtput with ?P after =>
    match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
  { unfold flag_pend_caller_restore_input, flag_pend_active_restore_input; Intros.
    sep_apply_l_atomic Hrecover; entailer!. }
  exact (Hpost after Houtput).
Qed.

Definition flag_waiting_publication_owner (environment : TaskStackCallEnvironment)
  sg reference call pointer post local pnode observed frame : Assertion :=
  pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) post.(TskState)
      (flag_continuation_local_node reference.(os_sched_call_stack)
        (flag_pend_waiting_receipt sg reference pointer call post) local))
    post.(TskState).(parkedTaskStacks) ** frame.

(** Produce the exact publication cut, then consume any actual completed
    suffix beginning at that same cut.  The forall is a partial-correctness
    consumer, not a promise that a suffix or a return exists.  The output
    receipt is the concrete node loan delivered by Hcall and Hnext. *)
Lemma flag_task_rdy_next_publish_return_consumer :
  forall (environment : TaskStackCallEnvironment) critical sg observer origin
    entry reference call pointer waiter old bits result c_result local fragments pnode frame
    before middle published observed,
  UCOS2_state_inv sg entry ->
  flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer call entry ->
  waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  (flag_task_rdy_fields_pre sg entry pointer waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg entry **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations) entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> pointer ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
    c_result = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    post.(FlagState).(flagWaitNodes) pointer = None /\
    flag_waiting_publication_owner environment sg reference call pointer post local pnode observed frame published /\
    forall stopped current after returned next_local return_frame saved acquired (packet : Prop),
      kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
        post published
        (flag_waiting_publication_owner environment sg reference call pointer post local pnode observed frame)
        stopped current after
        (coq_prop packet && flag_pend_caller_restore_input environment critical next_local
          (fun _ _ => flag_pend_waiting_receipt sg reference pointer call post ** return_frame) sg
          (FlagPendTaskCaller returned) returned saved acquired current) ->
      task_tcb_init_stack_same_call returned reference ->
      kernel_call_task_source returned current ->
      task_idle_ready sg current.(TskState) ->
      flag_pend_non_idle_at sg reference current ->
      (coq_prop packet && flag_pend_caller_restore_input environment critical next_local
        (fun returned current => flag_pend_wait_active sg reference pointer returned current ** return_frame) sg
        (FlagPendTaskCaller returned) returned saved acquired current) after.
Proof.
  intros environment critical sg observer origin entry reference call pointer waiter old bits result c_result
    local fragments pnode frame before middle published observed Hvalid Hdomain Hregistration Haddr
    Hresult Hparked Hcall Hnext Hpre.
  destruct (flag_task_rdy_next_publish_waiting_receipt _ _ _ environment.(task_stack_call_continuations)
    sg entry reference call pointer waiter old bits result c_result local fragments pnode frame
    before middle published observed Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hresult_c [Hobserved [Hnone Hpublished]]]]]].
  exists post, schedule; split; [exact Hstep|]. split; [exact Hresult_c|].
  split; [exact Hobserved|]. split; [exact Hnone|]. split; [exact Hpublished|].
  intros stopped current after returned next_local return_frame saved acquired packet run
    Hsame Hreturned Hidle Hnonidle.
  eapply flag_waiting_published_restore_owner; eassumption.
Qed.

(* The actual Task completion supplies the returned task source.  The
   prefix is the continuation of the published cut, and its bridge is a
   same-heap entailment into that completion's existing entry contract. *)
Lemma flag_waiting_published_task_completion :
  forall environment critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg reference original pointer entry bits result schedule post published input prefix_stop prefix_output
    frame install_call saved acquired other before installed sp actual,
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    install_call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi install_call.(InstallComponent.task_install_fields_context) **
    unmap_table_rep sg ** frame in
  forall (complete : InstallComponent.task_install_c_segment environment local sg rest
    install_call before installed sp actual)
    (prefix : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
      post published input prefix_stop install_call.(InstallComponent.task_install_fields_entry) before prefix_output),
  (prefix_output |-- InstallComponent.task_install_fields_entry_owner environment local sg install_call ** rest) ->
  kernel_program_selected_c_sequence_source environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  SelectedIdleComposition.kernel_program_selected_sequence_idle_source environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  flag_active_waiting_registration reference pointer original entry ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) ->
  task_in_range sg post.(TskState) ->
  post.(SchedState).(isRunning) = true ->
  task_idle_ready sg post.(TskState) ->
  flag_pend_non_idle_at sg reference post ->
  install_call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  task_stack_live_coverage install_call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key install_call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi install_call.(InstallComponent.task_install_fields_context)
    selected installed restored ->
  let current := InstallComponent.task_install_fields_current install_call in
  let returned := kernel_selected_call selected current in
  exists (whole : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
    post published input (orb prefix_stop false) current restored
    (coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original install_call.(InstallComponent.task_install_fields_entry) returned current) &&
     flag_pend_caller_restore_input environment critical other (fun _ _ => receipt ** frame) sg
       (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\
  (coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
    original install_call.(InstallComponent.task_install_fields_entry) returned current) &&
   flag_pend_caller_restore_input environment critical other
     (fun returned current => flag_pend_wait_active sg reference pointer returned current ** frame) sg
     (FlagPendTaskCaller returned) returned saved acquired current) restored.
Proof.
  intros environment critical task_abi sg reference original pointer entry bits result schedule post
    published input prefix_stop prefix_output frame install_call saved acquired other before installed sp actual
    receipt local rest complete prefix bridge Hprefix Hidle_prefix Hregistration Hresult Hstep
    Hrange Hrunning Hidle Hnonidle Hincoming Hcoverage.
  destruct (SelectedCompletionComposition.task_selected_completion_environment_sequence environment critical task_abi
    sg reference.(os_sched_call_invocation) reference.(os_sched_call_origin) None frame install_call original saved
    acquired receipt other before installed sp actual complete Hincoming Hcoverage) as [selected Hterminal].
  exists selected; intros restored Hrestore current returned.
  destruct (Hterminal restored Hrestore) as [tail [Htail [Hreturned Hsame]]].
  pose (whole := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix bridge tail).
  assert (Hwhole : kernel_program_selected_c_sequence_source environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) None _ _ _ _ _ _ _ whole).
  { unfold whole; apply KernelCSourceThen; assumption. }
  destruct (flag_active_task_rdy_waiting_registration sg entry reference original pointer bits result schedule post
    Hregistration Hstep) as [Hregistration_post Hnone].
  destruct Hregistration_post as [task [[Hsame_reference [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]].
  assert (Hreturned_reference : task_tcb_init_stack_same_call returned reference).
  { change (task_tcb_init_stack_same_call returned original) in Hsame.
    destruct Hsame as [Hi [Ho Hs]].
    destruct Hsame_reference as [Hi' [Ho' Hs']].
    split; [exact (eq_trans Hi Hi')|].
    split; [exact (eq_trans Ho Ho')|exact (eq_trans Hs Hs')]. }
  assert (Hstopped : orb prefix_stop false = false).
  { pose proof (kernel_program_selected_c_sequence_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ whole)
      as [_ Hstopped].
    pose proof (task_observer_lifetime_from_active sg post.(TskState)
      reference.(os_sched_call_invocation) reference.(os_sched_call_origin) Hrange Hactive) as Hlife.
    apply Bool.not_true_is_false; intro Hstop.
    apply (Hstopped Hlife Hstop).
    eapply kernel_call_same_return_observer_active; eassumption. }
  assert (Hprefix_stop : prefix_stop = false) by now rewrite Bool.orb_false_r in Hstopped.
  destruct (SelectedIdleComposition.kernel_program_selected_sequence_idle_source_transport environment critical sg
    reference _ _ _ _ _ _ _ prefix Hidle_prefix Horigin Hrunning Hprefix_stop)
    as [Hprefix_idle Hprefix_nonidle].
  destruct (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ tail))
    as [Hendpoint Hreturned_owner].
  destruct Hendpoint as [Hready [Hterminal_idle [Hterminal_nonidle [Hnormal Hcontrol]]]].
  (* The concrete install/take leaves the used tasks unchanged.  These two
     projections therefore apply without requiring the parked caller to
     be current at the install cut. *)
  assert (Hused : current.(TskState).(inUsedTaskStates) =
    install_call.(InstallComponent.task_install_fields_entry).(TskState).(inUsedTaskStates)) by reflexivity.
  assert (Hidle_current : task_idle_ready sg current.(TskState)).
  { unfold task_idle_ready; rewrite Hused; exact (Hprefix_idle Hidle). }
  assert (Hnonidle_current : flag_pend_non_idle_at sg reference current).
  { unfold flag_pend_non_idle_at; rewrite Hused; exact (Hprefix_nonidle Hnonidle). }
  exists whole; split; [exact Hwhole|]. split; [exact Hreturned|].
  eapply flag_waiting_published_restore_owner; eassumption.
Qed.

End FlagWaitingPublishedReturn.

Import FlagWaitingPublishedReturn.

Module FlagWaitingPublicationCompletion.

(** A consumer of actual completed suffixes, with the publication state,
    heap and owner fixed by the preceding literal C call.  This predicate
    neither asserts eventual return nor assumes a future active receipt. *)
Definition flag_waiting_published_task_continuation
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg reference original pointer post published input : Prop :=
  forall prefix_stop prefix_output frame install_call saved acquired other before installed sp actual,
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    install_call.(InstallComponent.task_install_fields_entry).(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi install_call.(InstallComponent.task_install_fields_context) **
    unmap_table_rep sg ** frame in
  forall (complete : InstallComponent.task_install_c_segment environment local sg rest
    install_call before installed sp actual)
    (prefix : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
      reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
      post published input prefix_stop install_call.(InstallComponent.task_install_fields_entry) before prefix_output),
  (prefix_output |-- InstallComponent.task_install_fields_entry_owner environment local sg install_call ** rest) ->
  kernel_program_selected_c_sequence_source environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  SelectedIdleComposition.kernel_program_selected_sequence_idle_source environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  install_call.(InstallComponent.task_install_fields_incoming) = original.(os_sched_call_stack) ->
  task_stack_live_coverage install_call.(InstallComponent.task_install_fields_entry).(TskState)
    (Some (task_stack_key install_call.(InstallComponent.task_install_fields_context).(os_sched_call_stack))) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi install_call.(InstallComponent.task_install_fields_context)
    selected installed restored ->
  let current := InstallComponent.task_install_fields_current install_call in
  let returned := kernel_selected_call selected current in
  exists (whole : kernel_c_sequence (kernel_program_selected_c_step environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
    post published input (orb prefix_stop false) current restored
    (coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
      original install_call.(InstallComponent.task_install_fields_entry) returned current) &&
     flag_pend_caller_restore_input environment critical other (fun _ _ => receipt ** frame) sg
       (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_selected_c_sequence_source environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\
  (coq_prop (flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
    original install_call.(InstallComponent.task_install_fields_entry) returned current) &&
   flag_pend_caller_restore_input environment critical other
     (fun returned current => flag_pend_wait_active sg reference pointer returned current ** frame) sg
     (FlagPendTaskCaller returned) returned saved acquired current) restored.

Lemma flag_task_rdy_next_publish_task_completion :
  forall (environment : TaskStackCallEnvironment) critical
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg entry reference original pointer waiter old bits result c_result local fragments pnode frame
    before middle published observed,
  UCOS2_state_inv sg entry ->
  entry.(SchedState).(isRunning) = true ->
  task_idle_ready sg entry.(TskState) ->
  flag_pend_non_idle_at sg reference entry ->
  flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer original entry ->
  waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  (flag_task_rdy_fields_pre sg entry pointer waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg entry **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations) entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> pointer ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
    c_result = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    post.(FlagState).(flagWaitNodes) pointer = None /\
    flag_waiting_publication_owner environment sg reference original pointer post local pnode observed frame published /\
    flag_waiting_published_task_continuation environment critical task_abi sg reference original pointer post published
      (flag_waiting_publication_owner environment sg reference original pointer post local pnode observed frame).
Proof.
  intros environment critical task_abi sg entry reference original pointer waiter old bits result c_result
    local fragments pnode frame before middle published observed Hvalid Hrunning Hidle Hnonidle
    Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext Hpre.
  destruct (flag_task_rdy_next_publish_waiting_receipt _ _ _ environment.(task_stack_call_continuations)
    sg entry reference original pointer waiter old bits result c_result local fragments pnode frame
    before middle published observed Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hresult_c [Hobserved [Hnone Hpublished]]]]]].
  assert (Hvalid_post : UCOS2_state_inv sg post).
  { assert (Hproject : flag_waiting_publication_owner environment sg reference original pointer post
        local pnode observed frame |-- coq_prop (UCOS2_state_inv sg post)).
    { unfold flag_waiting_publication_owner, UCOS2_fields_inv; entailer!. }
    exact (Hproject published Hpublished). }
  assert (Hrange : task_in_range sg post.(TskState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid_post; tauto. }
  assert (Hwake : WakeComponent.kernel_wake_c_source sg entry post).
  { eapply WakeComponent.KernelWakeCFlagSource; exact Hstep. }
  assert (Hrunning_post : post.(SchedState).(isRunning) = true).
  { destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
      as [actual_waiter [flags [actual_old [Hunlink [Hold [-> Hschedule]]]]]].
    exact Hrunning. }
  assert (Hidle_post : task_idle_ready sg post.(TskState)).
  { eapply SelectedIdleWakeStatus.kernel_wake_c_source_preserves_idle_ready; eassumption. }
  assert (Hnonidle_post : flag_pend_non_idle_at sg reference post).
  { eapply SelectedIdleFrames.task_used_priority_transport_non_idle; [|exact Hnonidle].
    eapply SelectedIdleWakeStatus.kernel_wake_c_source_used_priority_transport; exact Hwake. }
  exists post, schedule; split; [exact Hstep|]. split; [exact Hresult_c|].
  split; [exact Hobserved|]. split; [exact Hnone|]. split; [exact Hpublished|].
  unfold flag_waiting_published_task_continuation; intros.
  eapply flag_waiting_published_task_completion; eassumption.
Qed.

End FlagWaitingPublicationCompletion.

Import IRQAcquiredReturn IRQSelectedCompletion TerminalCallValue FlagWaitingPublishedReturn.

Module FlagWaitingPublishedIRQReturn.

(** The same publication suffix may finish through the actual IRQ selected
    completion.  Its handler fragment remains in the returned private frame. *)
Lemma flag_waiting_published_irq_completion :
  forall environment critical sg reference original pointer wake_entry bits result schedule post
    published input prefix_stop prefix_output handler entry transfer saved acquired other frame
    before prepared hooked_heap installed selected after source counter_prefix hook install restore,
  let actual_environment := task_sw_hook_call_environment environment in
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  forall (complete : kernel_irq_acquired_c_completion environment critical sg handler entry transfer
    original saved acquired receipt other frame before prepared hooked_heap installed selected after
    source counter_prefix hook install restore)
    (prefix : kernel_c_sequence (kernel_program_selected_c_step actual_environment critical sg
      reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
      post published input prefix_stop entry before prefix_output),
  (prefix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner actual_environment critical sg handler entry
    original saved acquired receipt other frame) ->
  kernel_program_selected_c_sequence_source actual_environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  SelectedIdleComposition.kernel_program_selected_sequence_idle_source actual_environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  flag_active_waiting_registration reference pointer original wake_entry ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg wake_entry pointer bits result = Some (schedule, post) ->
  task_in_range sg post.(TskState) ->
  post.(SchedState).(isRunning) = true ->
  task_idle_ready sg post.(TskState) ->
  flag_pend_non_idle_at sg reference post ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  exists (whole : kernel_c_sequence (kernel_program_selected_c_step actual_environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
    post published input (orb prefix_stop false) current after
    (irq_selected_suffix_output actual_environment critical sg handler transfer original saved acquired
      receipt other frame)),
  kernel_program_selected_c_sequence_source actual_environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\
  flag_pend_caller_restore_input actual_environment critical other
    (fun returned current => flag_pend_wait_active sg reference pointer returned current **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
    sg (FlagPendTaskCaller returned) returned saved acquired current after.
Proof.
  intros environment critical sg reference original pointer wake_entry bits result schedule post
    published input prefix_stop prefix_output handler entry transfer saved acquired other frame
    before prepared hooked_heap installed selected after source counter_prefix hook install restore
    actual_environment receipt complete prefix bridge Hprefix Hidle_prefix Hregistration Hresult Hstep
    Hrange Hrunning Hidle Hnonidle returned current.
  destruct (SelectedCompletionComposition.irq_acquired_completion_environment_sequence environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) None handler entry transfer original saved
    acquired receipt other frame before prepared hooked_heap installed selected after source counter_prefix hook
    install restore complete) as [tail [Htail [Hreturned [Hsame [Hready [Hlast_idle [Hlast_nonidle Hrest]]]]]]].
  pose (whole := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix bridge tail).
  assert (Hwhole : kernel_program_selected_c_sequence_source actual_environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) None _ _ _ _ _ _ _ whole).
  { unfold whole; apply KernelCSourceThen; assumption. }
  destruct (flag_active_task_rdy_waiting_registration sg wake_entry reference original pointer bits result schedule post
    Hregistration Hstep) as [Hregistration_post Hnone].
  destruct Hregistration_post as [task [[Hsame_reference [Horigin [Hlookup [Hgen [Hactive Hclear]]]]] Hpointer]].
  assert (Hreturned_reference : task_tcb_init_stack_same_call returned reference).
  { change (task_tcb_init_stack_same_call returned original) in Hsame.
    destruct Hsame as [Hi [Ho Hs]].
    destruct Hsame_reference as [Hi' [Ho' Hs']].
    split; [exact (eq_trans Hi Hi')|].
    split; [exact (eq_trans Ho Ho')|exact (eq_trans Hs Hs')]. }
  assert (Hstopped : orb prefix_stop false = false).
  { pose proof (kernel_program_selected_c_sequence_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ whole)
      as [_ Hstopped].
    pose proof (task_observer_lifetime_from_active sg post.(TskState)
      reference.(os_sched_call_invocation) reference.(os_sched_call_origin) Hrange Hactive) as Hlife.
    apply Bool.not_true_is_false; intro Hstop.
    apply (Hstopped Hlife Hstop).
    eapply kernel_call_same_return_observer_active; eassumption. }
  assert (Hprefix_stop : prefix_stop = false) by now rewrite Bool.orb_false_r in Hstopped.
  destruct (SelectedIdleComposition.kernel_program_selected_sequence_idle_source_transport actual_environment critical sg
    reference _ _ _ _ _ _ _ prefix Hidle_prefix Horigin Hrunning Hprefix_stop)
    as [Hprefix_idle Hprefix_nonidle].
  assert (Hidle_current : task_idle_ready sg current.(TskState)) by auto.
  assert (Hnonidle_current : flag_pend_non_idle_at sg reference current).
  { assert (Hentry_nonidle : flag_pend_non_idle_at sg original entry).
    { unfold flag_pend_non_idle_at; rewrite (proj2 (proj2 Hsame_reference)).
      exact (Hprefix_nonidle Hnonidle). }
    specialize (Hlast_nonidle Hentry_nonidle).
    change (flag_pend_non_idle_at sg returned current) in Hlast_nonidle.
    unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hreturned_reference)) in Hlast_nonidle.
    exact Hlast_nonidle. }
  pose proof (flag_waiting_published_receipt_active actual_environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) wake_entry reference original pointer
    bits result schedule post published input (orb prefix_stop false) current after _ returned Hregistration Hresult
    Hstep whole Hreturned_reference Hreturned Hidle_current Hnonidle_current) as Hrecover.
  fold receipt in Hrecover.
  pose proof (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ whole)) as Houtput.
  exists whole; split; [exact Hwhole|]. split; [exact Hreturned|].
  match type of Houtput with ?P after =>
    match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
  { unfold irq_selected_suffix_output, irq_selected_suffix_receipt,
      flag_pend_caller_restore_input, flag_pend_active_restore_input; Intros.
    sep_apply_l_atomic Hrecover; entailer!. }
  exact (Hpost after Houtput).
Qed.

End FlagWaitingPublishedIRQReturn.

Import FlagWaitingPublishedReturn FlagWaitingPublishedIRQReturn.

Module FlagWaitingPublicationIRQCompletion.

Definition flag_waiting_published_irq_continuation
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  sg reference original pointer post published input : Prop :=
  forall prefix_stop prefix_output handler entry transfer saved acquired other frame
    before prepared hooked_heap installed selected after source counter_prefix hook install restore,
  let actual_environment := task_sw_hook_call_environment environment in
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  forall (complete : kernel_irq_acquired_c_completion environment critical sg handler entry transfer
    original saved acquired receipt other frame before prepared hooked_heap installed selected after
    source counter_prefix hook install restore)
    (prefix : kernel_c_sequence (kernel_program_selected_c_step actual_environment critical sg
      reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
      post published input prefix_stop entry before prefix_output),
  (prefix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner actual_environment critical sg handler entry
    original saved acquired receipt other frame) ->
  kernel_program_selected_c_sequence_source actual_environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  SelectedIdleComposition.kernel_program_selected_sequence_idle_source actual_environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  exists (whole : kernel_c_sequence (kernel_program_selected_c_step actual_environment critical sg
    reference.(os_sched_call_invocation) reference.(os_sched_call_origin))
    post published input (orb prefix_stop false) current after
    (irq_selected_suffix_output actual_environment critical sg handler transfer original saved acquired
      receipt other frame)),
  kernel_program_selected_c_sequence_source actual_environment critical sg reference.(os_sched_call_invocation)
    reference.(os_sched_call_origin) None _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\
  flag_pend_caller_restore_input actual_environment critical other
    (fun returned current => flag_pend_wait_active sg reference pointer returned current **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
    sg (FlagPendTaskCaller returned) returned saved acquired current after.

Lemma flag_task_rdy_next_publish_irq_completion :
  forall (environment : TaskStackCallEnvironment) critical
    sg entry reference original pointer waiter old bits result c_result local fragments pnode frame
    before middle published observed,
  UCOS2_state_inv sg entry ->
  entry.(SchedState).(isRunning) = true ->
  task_idle_ready sg entry.(TskState) ->
  flag_pend_non_idle_at sg reference entry ->
  flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer original entry ->
  waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  (flag_task_rdy_fields_pre sg entry pointer waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg entry **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations) entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> pointer ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
    c_result = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    post.(FlagState).(flagWaitNodes) pointer = None /\
    flag_waiting_publication_owner (task_sw_hook_call_environment environment) sg reference original pointer post local pnode observed frame published /\
    flag_waiting_published_irq_continuation environment critical sg reference original pointer post published
      (flag_waiting_publication_owner (task_sw_hook_call_environment environment) sg reference original pointer post local pnode observed frame).
Proof.
  intros environment critical sg entry reference original pointer waiter old bits result c_result
    local fragments pnode frame before middle published observed Hvalid Hrunning Hidle Hnonidle
    Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext Hpre.
  destruct (flag_task_rdy_next_publish_waiting_receipt _ _ _ environment.(task_stack_call_continuations)
    sg entry reference original pointer waiter old bits result c_result local fragments pnode frame
    before middle published observed Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hresult_c [Hobserved [Hnone Hpublished]]]]]].
  assert (Hvalid_post : UCOS2_state_inv sg post).
  { assert (Hproject : flag_waiting_publication_owner (task_sw_hook_call_environment environment) sg reference original pointer post
        local pnode observed frame |-- coq_prop (UCOS2_state_inv sg post)).
    { unfold flag_waiting_publication_owner, UCOS2_fields_inv; entailer!. }
    exact (Hproject published Hpublished). }
  assert (Hrange : task_in_range sg post.(TskState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid_post; tauto. }
  assert (Hwake : WakeComponent.kernel_wake_c_source sg entry post).
  { eapply WakeComponent.KernelWakeCFlagSource; exact Hstep. }
  assert (Hrunning_post : post.(SchedState).(isRunning) = true).
  { destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hstep)
      as [actual_waiter [flags [actual_old [Hunlink [Hold [-> Hschedule]]]]]].
    exact Hrunning. }
  assert (Hidle_post : task_idle_ready sg post.(TskState)).
  { eapply SelectedIdleWakeStatus.kernel_wake_c_source_preserves_idle_ready; eassumption. }
  assert (Hnonidle_post : flag_pend_non_idle_at sg reference post).
  { eapply SelectedIdleFrames.task_used_priority_transport_non_idle; [|exact Hnonidle].
    eapply SelectedIdleWakeStatus.kernel_wake_c_source_used_priority_transport; exact Hwake. }
  exists post, schedule; split; [exact Hstep|]. split; [exact Hresult_c|].
  split; [exact Hobserved|]. split; [exact Hnone|]. split; [exact Hpublished|].
  unfold flag_waiting_published_irq_continuation; intros.
  eapply flag_waiting_published_irq_completion; eassumption.
Qed.

End FlagWaitingPublicationIRQCompletion.

Import PrimitiveComponent CriticalComponent PendPhaseCandidate SelectedCProgram SelectedCSource.
Import SelectedIRQWrapperSegment SelectedIRQWrapperSource SelectedReturnedCProgram SelectedReturnedCSource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource FlagTaskRdyNextCompletion.
Import FlagWaitingRecovery FlagWaitingPublishedReturn.

Module FlagWaitingPublicationEnvironment.

Definition selected_publication_environment_sequence
  environment critical sg observer origin state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped current after output) :
  kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    state before input stopped current after output :=
  kernel_program_environment_sequence_include environment critical sg observer origin _ _ _ _ _ _ _
    (kernel_program_returned_sequence_include environment critical sg observer origin _ _ _ _ _ _ _
      (kernel_program_wrapper_sequence_include environment critical sg observer origin _ _ _ _ _ _ _ run)).

Lemma selected_publication_environment_sequence_source :
  forall environment critical sg observer origin event_observer state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before input stopped current after output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _
    (selected_publication_environment_sequence environment critical sg observer origin _ _ _ _ _ _ _ run).
Proof.
  intros until run; intro Hsource; unfold selected_publication_environment_sequence.
  apply kernel_program_environment_sequence_include_source,
    kernel_program_returned_sequence_include_source,
    kernel_program_wrapper_sequence_include_source; exact Hsource.
Qed.

Lemma flag_task_rdy_next_publication_output_receipt :
  forall environment sg entry reference call pointer waiter bits result c_result schedule post local pnode observed frame,
  flag_active_waiting_registration reference pointer call entry ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) ->
  flag_task_rdy_next_output environment sg post reference call pointer waiter bits result c_result schedule
    local pnode observed frame |--
  flag_waiting_publication_owner environment sg reference call pointer post local pnode observed frame.
Proof.
  intros until frame; intros Hregistration Hresult Hstep.
  pose proof (flag_pend_task_rdy_wait_outcome sg entry reference call pointer bits result schedule post
    Hregistration Hresult Hstep) as Houtcome.
  unfold flag_task_rdy_next_output, flag_waiting_publication_owner; Intros.
  sep_apply_l_atomic (flag_pend_waiting_receipt_parked_map _ _ _ environment.(task_stack_call_continuations)
    sg reference pointer call post local Houtcome); entailer!.
Qed.

(** The original caller boundary is unchanged.  The two real C edges occupy
    before -> middle -> published; publication is an internal cut. *)
Lemma flag_task_rdy_next_outer_publication :
  forall (environment : TaskStackCallEnvironment) critical sg observer origin event_observer
    initial first_heap input prefix_stop prefix_output entry before
    reference call pointer waiter old bits result c_result local fragments pnode frame middle published observed
    (prefix : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      initial first_heap input prefix_stop entry before prefix_output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix ->
  (prefix_output |-- flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result
    local pnode frame) ->
  UCOS2_state_inv sg entry ->
  flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer call entry ->
  waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  exists post schedule
    (whole : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial first_heap input (orb prefix_stop false) post published
      (flag_waiting_publication_owner environment sg reference call pointer post local pnode observed frame)),
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ whole.
Proof.
  intros environment critical sg observer origin event_observer initial first_heap input prefix_stop prefix_output
    entry before reference call pointer waiter old bits result c_result local fragments pnode frame middle published
    observed prefix Hsource bridge Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext.
  pose proof (bridge before (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix)))
    as Hpre.
  destruct (flag_task_rdy_next_publish_waiting_receipt _ _ _ environment.(task_stack_call_continuations)
    sg entry reference call pointer waiter old bits result c_result local fragments pnode frame before middle published observed
    Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hresult_c [Hobserved [Hnone Hpublished]]]]]].
  pose (completion := @FlagTaskRdyNextCompletionCSegment environment sg entry reference call pointer waiter old bits result
    c_result local fragments pnode frame before middle published observed schedule post
    Hvalid Hdomain Hregistration Haddr Hparked Hcall Hnext Hpre Hstep).
  pose (atom := KernelCSequenceAtom _ _ _ _ _ _ _ _
    (@KernelProgramEnvironmentFlagTaskRdyNext environment critical sg observer origin _ _ _ _ _ _ _ completion)).
  pose (included := selected_publication_environment_sequence environment critical sg observer origin _ _ _ _ _ _ _ prefix).
  pose (combined := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ included bridge atom).
  pose proof (flag_task_rdy_next_publication_output_receipt environment sg entry reference call pointer waiter bits result
    c_result schedule post local pnode observed frame Hregistration Hresult Hstep) as close.
  pose proof (proj1 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix)) as Hinput.
  exists post, schedule, (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap H => H) combined close).
  split; [exact Hstep|]. unfold combined, atom.
  apply KernelCSourceAdapt, KernelCSourceThen.
  - apply selected_publication_environment_sequence_source; exact Hsource.
  - apply KernelCSourceAtom, KernelProgramEnvironmentFlagTaskRdyNextSource.
Qed.

Lemma flag_waiting_publication_actual_suffix :
  forall environment critical sg observer origin event_observer initial first_heap input first_stop
    post published publication last_stop current after output
    (prefix : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial first_heap input first_stop post published publication)
    (suffix : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      post published publication last_stop current after output),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ suffix ->
  exists (whole : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
    initial first_heap input (orb first_stop last_stop) current after output),
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ whole.
Proof.
  intros until suffix; intros Hprefix Hsuffix.
  pose (included := selected_publication_environment_sequence environment critical sg observer origin _ _ _ _ _ _ _ suffix).
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix (fun heap H => H) included).
  apply KernelCSourceThen; [exact Hprefix|].
  apply selected_publication_environment_sequence_source; exact Hsuffix.
Qed.

End FlagWaitingPublicationEnvironment.

Import FlagWaitingPublicationEnvironment SelectedIdleComposition.

Module FlagWaitingPublicationPrefix.

Lemma flag_task_rdy_next_c_segment_idle_non_idle :
  forall environment sg observed entry before input stopped post after output,
  flag_task_rdy_next_c_segment environment sg entry before input stopped post after output ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg post.(TskState)) /\
  (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed post).
Proof.
  intros until output; intro Hsegment.
  pose proof (proj2 (flag_task_rdy_next_c_segment_source _ _ _ _ _ _ _ _ _ Hsegment)) as Hsource.
  destruct Hsegment.
  split.
  - intro Hidle; eapply SelectedIdleWakeStatus.kernel_wake_c_source_preserves_idle_ready; eassumption.
  - intro Hnonidle; eapply SelectedIdleFrames.task_used_priority_transport_non_idle; [|exact Hnonidle].
    eapply SelectedIdleWakeStatus.kernel_wake_c_source_used_priority_transport; exact Hsource.
Qed.

Section Prefix.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (observer : nat) (origin : TaskInvocationOrigin).
Let segment := kernel_program_environment_c_step environment critical sg observer origin.

Inductive flag_waiting_publication_prefix :
  forall entry before input stopped current after output,
  kernel_c_sequence segment entry before input stopped current after output -> Prop :=
| FlagWaitingPrefixSelected : forall entry before input stopped current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      entry before input stopped current after output),
    kernel_program_selected_sequence_idle_source environment critical sg observer origin _ _ _ _ _ _ _ run ->
    flag_waiting_publication_prefix entry before input stopped current after output
      (selected_publication_environment_sequence environment critical sg observer origin _ _ _ _ _ _ _ run)
| FlagWaitingPrefixPublication : forall entry before input stopped current after output
    (completion : flag_task_rdy_next_c_segment environment sg entry before input stopped current after output),
    flag_waiting_publication_prefix entry before input stopped current after output
      (KernelCSequenceAtom segment _ _ _ _ _ _ _
        (@KernelProgramEnvironmentFlagTaskRdyNext environment critical sg observer origin _ _ _ _ _ _ _ completion))
| FlagWaitingPrefixThen : forall entry before input first_stop middle middle_heap first_output next_input
    last_stop current after output
    (first : kernel_c_sequence segment entry before input first_stop middle middle_heap first_output)
    (bridge : first_output |-- next_input)
    (last : kernel_c_sequence segment middle middle_heap next_input last_stop current after output),
    flag_waiting_publication_prefix _ _ _ _ _ _ _ first ->
    flag_waiting_publication_prefix _ _ _ _ _ _ _ last ->
    flag_waiting_publication_prefix entry before input (orb first_stop last_stop) current after output
      (KernelCSequenceThen segment _ _ _ _ _ _ _ _ _ _ _ _ first bridge last)
| FlagWaitingPrefixAdapt : forall entry before input inner_input stopped current after inner_output output
    (owned : input before) (open_input : input |-- inner_input)
    (inner : kernel_c_sequence segment entry before inner_input stopped current after inner_output)
    (close_output : inner_output |-- output),
    flag_waiting_publication_prefix _ _ _ _ _ _ _ inner ->
    flag_waiting_publication_prefix entry before input stopped current after output
      (KernelCSequenceAdapt segment _ _ _ _ _ _ _ _ _ owned open_input inner close_output).
End Prefix.

Lemma flag_waiting_publication_prefix_idle_non_idle :
  forall environment critical sg observed entry before input stopped current after output
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin)) entry before input stopped current after output),
  flag_waiting_publication_prefix environment critical sg observed.(os_sched_call_invocation)
    observed.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  observed.(os_sched_call_origin) = RunningInvocation observed.(os_sched_call_stack).(stackLeaseSlot)
    observed.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(SchedState).(isRunning) = true -> stopped = false ->
  (task_idle_ready sg entry.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg observed entry -> flag_pend_non_idle_at sg observed current).
Proof.
  intros environment critical sg observed entry before input stopped current after output run Hprefix Horigin.
  induction Hprefix; intros Hrunning Hstop.
  - eapply kernel_program_selected_sequence_idle_source_transport; eassumption.
  - eapply flag_task_rdy_next_c_segment_idle_non_idle; exact completion.
  - apply Bool.orb_false_iff in Hstop; destruct Hstop as [Hfirst Hlast].
    destruct (IHHprefix1 Hrunning Hfirst) as [Hidle Hnonidle].
    assert (Hmiddle : middle.(SchedState).(isRunning) = true).
    { rewrite (kernel_program_environment_c_sequence_running environment critical sg
        observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ first).
      exact Hrunning. }
    destruct (IHHprefix2 Hmiddle Hlast) as [Hidle' Hnonidle']; split; auto.
  - apply IHHprefix; assumption.
Qed.

Lemma flag_waiting_publication_completed_idle_non_idle :
  forall environment critical sg original returned state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin)) state before input stopped current after output),
  flag_waiting_publication_prefix environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg state.(TskState) -> kernel_call_task_source original state ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_normal_return original state returned current -> kernel_call_task_source returned current ->
  stopped = false /\
  (task_idle_ready sg state.(TskState) -> task_idle_ready sg current.(TskState)) /\
  (flag_pend_non_idle_at sg original state -> flag_pend_non_idle_at sg returned current).
Proof.
  intros environment critical sg original returned state before input stopped current after output run
    Hsource Hrange Horiginal Hrunning Hnormal Hreturned.
  assert (Hstop : stopped = false).
  { eapply sched_observer_spec.kernel_call_completed_task_source_not_stopped;
      [exact Hrange|exact Horiginal| |exact Hnormal|exact Hreturned].
    eapply kernel_program_environment_c_sequence_observer_lifetime; exact run. }
  destruct (flag_waiting_publication_prefix_idle_non_idle environment critical sg original
    _ _ _ _ _ _ _ run Hsource (proj1 Horiginal) Hrunning Hstop) as [Hidle Hnonidle].
  split; [exact Hstop|]. split; [exact Hidle|].
  intro Hinitial; specialize (Hnonidle Hinitial).
  unfold flag_pend_non_idle_at in *.
  rewrite (proj2 (proj2 (proj1 Hnormal))); exact Hnonidle.
Qed.

Lemma flag_task_rdy_next_outer_publication_prefix :
  forall (environment : TaskStackCallEnvironment) critical sg observer origin event_observer
    initial first_heap input prefix_stop prefix_output entry before
    reference call pointer waiter old bits result c_result local fragments pnode frame middle published observed
    (prefix : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      initial first_heap input prefix_stop entry before prefix_output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ prefix ->
  kernel_program_selected_sequence_idle_source environment critical sg observer origin _ _ _ _ _ _ _ prefix ->
  (prefix_output |-- flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result
    local pnode frame) ->
  UCOS2_state_inv sg entry ->
  flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer call entry ->
  waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  exists post schedule
    (whole : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer origin)
      initial first_heap input (orb prefix_stop false) post published
      (flag_waiting_publication_owner environment sg reference call pointer post local pnode observed frame)),
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
  kernel_program_environment_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ whole /\
  flag_waiting_publication_prefix environment critical sg observer origin _ _ _ _ _ _ _ whole.
Proof.
  intros environment critical sg observer origin event_observer initial first_heap input prefix_stop prefix_output
    entry before reference call pointer waiter old bits result c_result local fragments pnode frame middle published
    observed prefix Hsource Hidle bridge Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext.
  pose proof (bridge before (proj2 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix)))
    as Hpre.
  destruct (flag_task_rdy_next_publish_waiting_receipt _ _ _ environment.(task_stack_call_continuations)
    sg entry reference call pointer waiter old bits result c_result local fragments pnode frame before middle published observed
    Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hresult_c [Hobserved [Hnone Hpublished]]]]]].
  pose (completion := @FlagTaskRdyNextCompletionCSegment environment sg entry reference call pointer waiter old bits result
    c_result local fragments pnode frame before middle published observed schedule post
    Hvalid Hdomain Hregistration Haddr Hparked Hcall Hnext Hpre Hstep).
  pose (atom := KernelCSequenceAtom _ _ _ _ _ _ _ _
    (@KernelProgramEnvironmentFlagTaskRdyNext environment critical sg observer origin _ _ _ _ _ _ _ completion)).
  pose (included := selected_publication_environment_sequence environment critical sg observer origin _ _ _ _ _ _ _ prefix).
  pose (combined := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ included bridge atom).
  pose proof (flag_task_rdy_next_publication_output_receipt environment sg entry reference call pointer waiter bits result
    c_result schedule post local pnode observed frame Hregistration Hresult Hstep) as close.
  pose proof (proj1 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix)) as Hinput.
  exists post, schedule, (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap H => H) combined close).
  split; [exact Hstep|]. split.
  - unfold combined, atom; apply KernelCSourceAdapt, KernelCSourceThen.
    + apply selected_publication_environment_sequence_source; exact Hsource.
    + apply KernelCSourceAtom, KernelProgramEnvironmentFlagTaskRdyNextSource.
  - unfold combined, atom; apply FlagWaitingPrefixAdapt, FlagWaitingPrefixThen.
    + apply FlagWaitingPrefixSelected; exact Hidle.
    + apply FlagWaitingPrefixPublication.
Qed.

End FlagWaitingPublicationPrefix.

Import PrimitiveComponent CriticalComponent TerminalCallValue TerminalReturn FlagPendSchedulerResources.
Import SelectedCProgram SelectedCSource SelectedReturnPrimitive SelectedCompletionSource.
Import TaskSelectedCompletion SelectedCompletionSuffix SelectedCompletionComposition SelectedOuterCompletion.
Import SelectedEndpointObservations SelectedEnvironmentBuilder SelectedCallerPreservation SelectedIdleComposition.
Import IRQAcquiredReturn IRQSelectedCompletion FlagWaitingPublicationEnvironment FlagWaitingPublicationPrefix.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource.

Module FlagWaitingOuterCompletion.

Lemma irq_published_completion_outer_sequence :
  forall environment critical sg event_observer handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore
    initial first_heap input prefix_stop prefix_output
    (run : kernel_c_sequence (kernel_program_environment_c_step (task_sw_hook_call_environment environment) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input prefix_stop entry before prefix_output)
    (bridge : prefix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner
      (task_sw_hook_call_environment environment) critical sg handler entry original saved acquired receipt other frame),
  kernel_program_environment_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run ->
  flag_waiting_publication_prefix (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  kernel_irq_acquired_c_completion environment critical sg handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore ->
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_fragments) in
  let current := os_int_exit_installed_state transfer in
  exists (whole : kernel_c_sequence (kernel_program_environment_c_step (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) initial first_heap input
    (orb prefix_stop false) current after
    (coq_prop (flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
       (FlagPendTaskCaller original) original initial returned current) &&
      irq_selected_suffix_output (task_sw_hook_call_environment environment) critical sg handler transfer
        original saved acquired receipt other frame)),
  kernel_program_environment_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ whole /\
  flag_waiting_publication_prefix (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\ orb prefix_stop false = false.
Proof.
  intros environment critical sg event_observer handler entry transfer original saved acquired receipt other frame
    before prepared hooked_heap installed selected after source prefix hook install restore initial first_heap input prefix_stop
    prefix_output run bridge Hsource Hidle Hrange Horiginal Hrunning Henabled complete returned current.
  pose (primitive := @KernelIRQAcquiredReturnCStep environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete).
  pose (step := @KernelSelectedProgramIRQ critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
    environment _ _ _ _ _ _ _ primitive).
  pose (selected_tail := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  pose (tail := selected_publication_environment_sequence (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ selected_tail).
  pose (all := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run bridge tail).
  assert (Hall_source : kernel_program_environment_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ all).
  { unfold all; apply KernelCSourceThen; [exact Hsource|].
    apply selected_publication_environment_sequence_source, KernelCSourceAtom; unfold step; apply KernelSelectedProgramIRQSource. }
  assert (Hall_idle : flag_waiting_publication_prefix (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ all).
  { unfold all; apply FlagWaitingPrefixThen; [exact Hidle|].
    apply FlagWaitingPrefixSelected, KernelCSourceAtom; unfold step; apply KernelSelectedIRQIdleSource. }
  destruct (kernel_irq_acquired_c_completion_task_source environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [Hreturned Hsame].
  destruct (irq_acquired_c_completion_endpoint_facts environment critical sg handler entry transfer original saved acquired
    receipt other frame before prepared hooked_heap installed selected after source prefix hook install restore complete)
    as [Hready [_ [_ [Hnormal [Hrunning_last Henabled_last]]]]].
  destruct (flag_waiting_publication_completed_idle_non_idle (task_sw_hook_call_environment environment) critical sg
    original returned _ _ _ _ _ _ _ all Hall_idle Hrange Horiginal Hrunning (Hnormal initial) Hreturned)
    as [Hstop [Hidle_all Hnonidle_all]].
  assert (Hendpoint : flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
    (FlagPendTaskCaller original) original initial returned current).
  { split; [intros; exact Hready|]. split; [intros [_ Hinitial]; exact (Hidle_all Hinitial)|].
    split; [intros [_ Hinitial]; exact (Hnonidle_all Hinitial)|].
    split; [apply Hnormal|]. intros _.
    eapply kernel_call_enabled_control_rely; [exact Henabled|exact Henabled_last|].
    eapply kernel_program_environment_c_sequence_running; exact all. }
  pose proof (proj1 (kernel_program_environment_c_sequence_resources (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ all)) as Hinput.
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) all
    (fun heap Howner => conj Hendpoint Howner)).
  split; [apply KernelCSourceAdapt; exact Hall_source|].
  split; [apply FlagWaitingPrefixAdapt; exact Hall_idle|]. exact (conj Hreturned Hstop).
Qed.

(** The full last selector is retained in the call record's own context,
    outgoing/incoming stacks and hooked state.  It supplies final enabled;
    Running comes from this actual prefix rather than counter-frame claims. *)
Lemma task_published_completion_outer_sequence :
  forall environment critical
    (task_abi : Armv7aTaskContextABI (task_sw_hook_call_environment environment).(task_stack_call_external)
      (task_sw_hook_call_environment environment).(task_stack_call_platform)
      (task_sw_hook_call_environment environment).(task_stack_call_port)
      (task_sw_hook_call_environment environment).(task_stack_call_continuations))
    sg event_observer frame original saved acquired receipt other initial first_heap input prefix_stop prefix_output
    last_entry context saved_sp outgoing hooked incoming resumed
    (Hswitch : os_sched_requests_switch last_entry = true)
    (Hsave : (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_arch_save_source)
      context saved_sp outgoing)
    (Hhook : kernel_client_step (task_sw_hook_call_environment environment).(task_stack_call_external).(os_sched_hook_action)
      sg (os_sched_save_current_sp (os_sched_prefix_state last_entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked)
    (Hdestination : os_sched_destination_binding (task_sw_hook_call_environment environment).(task_stack_call_external)
      context outgoing hooked incoming resumed),
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := incoming;
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  let local := kernel_sched_saved_local_resource_at (task_sw_hook_call_environment environment).(task_stack_call_platform)
    critical sg hooked.(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame in
  forall before installed sp actual
    (complete : InstallComponent.task_install_c_segment (task_sw_hook_call_environment environment) local sg rest
      call before installed sp actual)
    (run : kernel_c_sequence (kernel_program_environment_c_step (task_sw_hook_call_environment environment) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap input prefix_stop hooked before prefix_output)
    (bridge : prefix_output |-- InstallComponent.task_install_fields_entry_owner
      (task_sw_hook_call_environment environment) local sg call ** rest),
  kernel_program_environment_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ run ->
  flag_waiting_publication_prefix (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ run ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  incoming = original.(os_sched_call_stack) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  exists (whole : kernel_c_sequence (kernel_program_environment_c_step (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) initial first_heap input
    (orb prefix_stop false) current restored
    (coq_prop (flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
       (FlagPendTaskCaller original) original initial returned current) &&
      flag_pend_caller_restore_input (task_sw_hook_call_environment environment) critical other
        (fun _ _ => receipt ** frame) sg (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_environment_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\ orb prefix_stop false = false.
Proof.
  intros environment critical task_abi sg event_observer frame original saved acquired receipt other initial first_heap input
    prefix_stop prefix_output last_entry context saved_sp outgoing hooked incoming resumed Hswitch Hsave Hhook Hdestination
    call local rest before installed sp actual complete run bridge Hsource Hidle Hrange Horiginal Hrunning Henabled Hincoming Hcoverage.
  pose proof (proj2 (InstallComponent.task_install_c_segment_resources (task_sw_hook_call_environment environment)
    local sg rest call before installed sp actual complete)) as Hpost.
  destruct (task_install_fields_installed_owner_selected (task_sw_hook_call_environment environment)
    local sg rest call installed Hpost) as [selected Hselected].
  exists selected; intros restored Hrestore current returned.
  destruct (task_selected_c_environment_return (task_sw_hook_call_environment environment) critical task_abi sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer frame call original saved acquired receipt other
    before installed sp actual selected restored complete Hselected Hincoming Hcoverage Hrestore)
    as [old_tail [Hold_tail [Hreturned Hsame]]].
  destruct (kernel_program_return_sequence_include_acquired_irq_source (task_sw_hook_call_environment environment)
    critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer
    _ _ _ _ _ _ _ old_tail Hold_tail) as [selected_tail Hselected_tail].
  pose (tail := selected_publication_environment_sequence (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ selected_tail).
  pose proof (selected_publication_environment_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ selected_tail Hselected_tail) as Htail.
  pose (all := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ run bridge tail).
  assert (Hall_source : kernel_program_environment_c_sequence_source (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) event_observer _ _ _ _ _ _ _ all).
  { unfold all; apply KernelCSourceThen; assumption. }
  destruct (task_selected_c_completion_ready_normal (task_sw_hook_call_environment environment) critical task_abi sg
    frame call original saved acquired receipt other before installed sp actual selected restored complete
    Hselected Hincoming Hcoverage Hrestore) as [Hready Hnormal].
  assert (Hstop : orb prefix_stop false = false).
  { eapply kernel_call_completed_task_source_not_stopped; [exact Hrange|exact Horiginal| |apply Hnormal|exact Hreturned].
    eapply kernel_program_environment_c_sequence_observer_lifetime; exact all. }
  assert (Hprefix_stop : prefix_stop = false) by now rewrite Bool.orb_false_r in Hstop.
  destruct (flag_waiting_publication_prefix_idle_non_idle (task_sw_hook_call_environment environment)
    critical sg original _ _ _ _ _ _ _ run Hidle (proj1 Horiginal) Hrunning Hprefix_stop) as [Hprefix_idle Hprefix_nonidle].
  assert (Hcontrol : kernel_call_control_rely sg initial current).
  { eapply kernel_call_enabled_control_rely; [exact Henabled| |].
    - change (os_sched_selection_enabled hooked = true).
      change (hooked = os_sched_save_current_sp (os_sched_prefix_state last_entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) in Hhook.
      rewrite Hhook. change (os_sched_selection_enabled last_entry = true).
      exact (proj1 (proj1 (os_sched_requests_switch_iff last_entry) Hswitch)).
    - change (hooked.(SchedState).(isRunning) = initial.(SchedState).(isRunning)).
      eapply kernel_program_environment_c_sequence_running; exact run. }
  assert (Hendpoint : flag_pend_call_endpoint_observations (task_sw_hook_call_environment environment) sg
    (FlagPendTaskCaller original) original initial returned current).
  { split; [intros; exact Hready|].
    split; [intros [_ Hinitial]; exact (Hprefix_idle Hinitial)|].
    split.
    - intros [_ Hinitial].
      pose proof (Hprefix_nonidle Hinitial) as Hmiddle.
      unfold flag_pend_non_idle_at in Hmiddle.
      rewrite <- (proj2 (proj2 Hsame)) in Hmiddle; exact Hmiddle.
    - split; [exact (Hnormal initial)|]. intros _; exact Hcontrol. }
  pose proof (proj1 (kernel_program_environment_c_sequence_resources (task_sw_hook_call_environment environment) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ all)) as Hinput.
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap Howner => Howner) all
    (fun heap Howner => conj Hendpoint Howner)).
  split; [apply KernelCSourceAdapt; exact Hall_source|]. exact (conj Hreturned Hstop).
Qed.


End FlagWaitingOuterCompletion.

Import FlagWaitingPublishedReturn FlagWaitingPublicationPrefix FlagWaitingOuterCompletion.

Module FlagWaitingPublicationReceipt.

(** Only the concrete terminal's unchanged task fields and Flag state are
    used here.  The suffix begins at the heap published by the actual
    TaskRdy/Next pair, and its receipt is the resulting private node loan. *)
Lemma flag_waiting_published_terminal_receipt :
  forall environment critical sg observer origin entry reference call pointer bits result schedule post
    published input stopped terminal_entry terminal_heap output returned current,
  flag_active_waiting_registration reference pointer call entry ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) ->
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    post published input stopped terminal_entry terminal_heap output ->
  current.(TskState).(inUsedTaskStates) = terminal_entry.(TskState).(inUsedTaskStates) ->
  current.(FlagState) = terminal_entry.(FlagState) ->
  task_tcb_init_stack_same_call returned reference ->
  kernel_call_task_source returned current ->
  flag_pend_waiting_receipt sg reference pointer call post |--
    flag_pend_waiting_receipt sg reference pointer returned current.
Proof.
  intros until current; intros Hregistration Hresult Hstep suffix Hused Hflags Hsame Hreturned.
  destruct (flag_active_task_rdy_waiting_registration sg entry reference call pointer bits result schedule post
    Hregistration Hstep) as [_ Hnone].
  assert (Hcurrent_none : current.(FlagState).(flagWaitNodes) pointer = None).
  { rewrite Hflags; eapply flag_wait_nodes_included_absent;
      [eapply kernel_program_selected_c_sequence_nodes_included; exact suffix|exact Hnone]. }
  assert (Hfields : FlagWaitingSuccessor.flag_pend_detached_fields_at_origin reference.(os_sched_call_origin) current).
  { pose proof (flag_task_rdy_selected_sequence_detached_fields environment critical sg observer origin
      entry reference call pointer bits result schedule post published input stopped terminal_entry terminal_heap output
      Hregistration Hresult Hstep suffix) as Hterminal.
    unfold FlagWaitingSuccessor.flag_pend_detached_fields_at_origin in *.
    destruct reference.(os_sched_call_origin); try exact I.
    intros; rewrite Hused in *; eapply Hterminal; eassumption. }
  eapply flag_pend_detached_receipt_current; eassumption.
Qed.

Lemma flag_waiting_save_input_idle_non_idle :
  forall environment critical local sg reference pointer original mask initial private,
  flag_pend_caller_save_input environment critical local (flag_pend_wait_active sg reference pointer) sg
    (FlagPendTaskCaller original) original mask initial ** private |--
  coq_prop (task_idle_ready sg initial.(TskState) /\ flag_pend_non_idle_at sg reference initial).
Proof.
  intros; unfold flag_pend_caller_save_input, flag_pend_active_save_input, flag_pend_wait_active; entailer!.
Qed.

Lemma flag_waiting_outer_endpoint_active :
  forall environment sg reference pointer original returned initial current receipt,
  kernel_call_task_source original initial ->
  task_tcb_init_stack_same_call original reference ->
  flag_pend_call_endpoint_observations environment sg
    (FlagPendTaskCaller original) original initial returned current ->
  task_idle_ready sg initial.(TskState) -> flag_pend_non_idle_at sg reference initial ->
  (receipt |-- flag_pend_waiting_receipt sg reference pointer returned current) ->
  receipt |-- flag_pend_wait_active sg reference pointer returned current.
Proof.
  intros environment sg reference pointer original returned initial current receipt
    Horiginal Hsame Hendpoint Hidle Hnonidle Hreceipt.
  destruct Hendpoint as [Hready [Hidle_after [Hnonidle_after [Hnormal Hcontrol]]]].
  assert (Hinitial_nonidle : flag_pend_non_idle_at sg original initial).
  { unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hsame)); exact Hnonidle. }
  specialize (Hidle_after (conj Horiginal Hidle)).
  specialize (Hnonidle_after (conj Horiginal Hinitial_nonidle)).
  assert (Hcurrent_nonidle : flag_pend_non_idle_at sg reference current).
  { unfold flag_pend_non_idle_at in *.
    rewrite (proj2 (proj2 (proj1 Hnormal))), (proj2 (proj2 Hsame)) in Hnonidle_after.
    exact Hnonidle_after. }
  sep_apply_l_atomic Hreceipt.
  unfold flag_pend_waiting_receipt, flag_pend_wait_active; entailer!.
Qed.

End FlagWaitingPublicationReceipt.

Import FlagWaitingPublicationReceipt.

Module FlagWaitingPublishedCalls.

(** This is the missing linked-to-detached case.  The publication heap is
    computed from the literal TaskRdy and Next calls.  The continuation is
    universally quantified over actual completed suffixes; no return or
    future receipt is assumed. *)
Lemma flag_task_rdy_next_task_return :
  forall environment critical
    (task_abi : Armv7aTaskContextABI (task_sw_hook_call_environment environment).(task_stack_call_external)
      (task_sw_hook_call_environment environment).(task_stack_call_platform)
      (task_sw_hook_call_environment environment).(task_stack_call_port)
      (task_sw_hook_call_environment environment).(task_stack_call_continuations))
    sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed,
  let env := task_sw_hook_call_environment environment in
  let active := flag_pend_wait_active sg reference pointer in
  let input := flag_pend_caller_save_input env critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private in
  forall (prefix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input prefix_stop entry before prefix_output),
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  (prefix_output |-- flag_task_rdy_next_input env sg entry reference original pointer waiter old bits result
    publication_local pnode publication_frame) ->
  UCOS2_state_inv sg entry -> flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer original entry -> waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  exists post schedule,
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
  forall suffix_stop suffix_output frame other last_entry context saved_sp outgoing hooked incoming resumed
    (Hswitch : os_sched_requests_switch last_entry = true)
    (Hsave : env.(task_stack_call_external).(os_sched_arch_save_source) context saved_sp outgoing)
    (Hhook : kernel_client_step env.(task_stack_call_external).(os_sched_hook_action) sg
      (os_sched_save_current_sp (os_sched_prefix_state last_entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked)
    (Hdestination : os_sched_destination_binding env.(task_stack_call_external)
      context outgoing hooked incoming resumed),
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := incoming;
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  let local := kernel_sched_saved_local_resource_at env.(task_stack_call_platform)
    critical sg hooked.(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame in
  forall installed_heap installed sp actual
    (complete : InstallComponent.task_install_c_segment env local sg rest call installed_heap installed sp actual)
    (suffix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      post published (flag_waiting_publication_owner env sg reference original pointer post publication_local
        pnode observed publication_frame) suffix_stop hooked installed_heap suffix_output),
  (suffix_output |-- InstallComponent.task_install_fields_entry_owner env local sg call ** rest) ->
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ suffix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ suffix ->
  incoming = original.(os_sched_call_stack) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  exists (whole : kernel_c_sequence (kernel_program_environment_c_step env critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) initial first_heap input
    (orb (orb (orb prefix_stop false) suffix_stop) false) current restored
    (coq_prop (flag_pend_call_endpoint_observations env sg (FlagPendTaskCaller original)
      original initial returned current) &&
     flag_pend_caller_restore_input env critical other (fun _ _ => receipt ** frame) sg
       (FlagPendTaskCaller returned) returned saved acquired current)),
  kernel_program_environment_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\
  (receipt |-- active returned current).
Proof.
  intros environment critical task_abi sg reference original pointer initial first_heap initial_local initial_private
    saved acquired prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments
    pnode publication_frame middle published observed env active input prefix Hprefix Hprefix_idle bridge Hvalid Hdomain
    Hregistration Haddr Hresult Hparked Hcall Hnext Hrange Horiginal Hrunning Henabled.
  destruct (flag_task_rdy_next_outer_publication_prefix env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None initial first_heap input prefix_stop prefix_output entry before reference original
    pointer waiter old bits result c_result publication_local fragments pnode publication_frame middle published observed
    prefix Hprefix Hprefix_idle bridge Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext)
    as [post [schedule [publication [Hstep [Hpublication_source Hpublication_idle]]]]].
  pose proof (proj1 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix)) as Hinput.
  destruct (flag_waiting_save_input_idle_non_idle env critical initial_local sg reference pointer original
    (armv7a_irq_fiq_mask saved) initial initial_private first_heap Hinput) as [Hidle Hnonidle].
  assert (Hsame_original : task_tcb_init_stack_same_call original reference).
  { destruct Hregistration as [task [[Hsame _] _]]; exact Hsame. }
  exists post, schedule; split; [exact Hstep|].
  intros suffix_stop suffix_output frame other last_entry context saved_sp outgoing hooked incoming resumed Hswitch Hsave
    Hhook Hdestination call receipt local rest installed_heap installed sp actual complete suffix suffix_bridge Hsuffix
    Hsuffix_idle Hincoming Hcoverage.
  pose (included := selected_publication_environment_sequence env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ suffix).
  pose (combined := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ publication (fun heap H => H) included).
  assert (Hcombined : kernel_program_environment_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ combined).
  { unfold combined; apply KernelCSourceThen; [exact Hpublication_source|].
    apply selected_publication_environment_sequence_source; exact Hsuffix. }
  assert (Hcombined_idle : flag_waiting_publication_prefix env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ combined).
  { unfold combined; apply FlagWaitingPrefixThen; [exact Hpublication_idle|].
    apply FlagWaitingPrefixSelected; exact Hsuffix_idle. }
  destruct (task_published_completion_outer_sequence environment critical task_abi sg None frame original saved acquired
    receipt other initial first_heap input _ suffix_output last_entry context saved_sp outgoing hooked incoming resumed
    Hswitch Hsave Hhook Hdestination installed_heap installed sp actual complete combined suffix_bridge
    Hcombined Hcombined_idle Hrange Horiginal Hrunning Henabled Hincoming Hcoverage) as [selected Hterminal].
  exists selected; intros restored Hrestore current returned.
  destruct (Hterminal restored Hrestore) as [whole [Hwhole [Hreturned Hstop]]].
  destruct (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ whole))
    as [Hendpoint Howner].
  assert (Hsame_returned : task_tcb_init_stack_same_call returned reference).
  { destruct (proj1 (proj2 (proj2 (proj2 Hendpoint)))) as [Hsame Havailable].
    destruct Hsame as [Hi [Ho Hs]], Hsame_original as [Hi' [Ho' Hs']].
    repeat split; [exact (eq_trans Hi Hi')|exact (eq_trans Ho Ho')|exact (eq_trans Hs Hs')]. }
  assert (Hreceipt : receipt |-- flag_pend_waiting_receipt sg reference pointer returned current).
  { eapply flag_waiting_published_terminal_receipt; [exact Hregistration|exact Hresult|exact Hstep|exact suffix| | |exact Hsame_returned|exact Hreturned]; reflexivity. }
  exists whole; split; [exact Hwhole|]. split; [exact Hreturned|].
  exact (flag_waiting_outer_endpoint_active env sg reference pointer original returned initial current receipt
    Horiginal Hsame_original Hendpoint Hidle Hnonidle Hreceipt).
Qed.

Lemma flag_task_rdy_next_irq_return :
  forall environment critical sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed,
  let env := task_sw_hook_call_environment environment in
  let active := flag_pend_wait_active sg reference pointer in
  let input := flag_pend_caller_save_input env critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private in
  forall (prefix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input prefix_stop entry before prefix_output),
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  (prefix_output |-- flag_task_rdy_next_input env sg entry reference original pointer waiter old bits result
    publication_local pnode publication_frame) ->
  UCOS2_state_inv sg entry -> flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer original entry -> waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  exists post schedule,
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
  forall suffix_stop suffix_output handler irq_entry transfer other frame irq_before prepared hooked_heap installed selected after
    source irq_prefix hook install restore,
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  forall (suffix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    post published (flag_waiting_publication_owner env sg reference original pointer post publication_local
      pnode observed publication_frame) suffix_stop irq_entry irq_before suffix_output),
  (suffix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner env critical sg handler irq_entry original
    saved acquired receipt other frame) ->
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ suffix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ suffix ->
  kernel_irq_acquired_c_completion environment critical sg handler irq_entry transfer original saved acquired receipt other frame
    irq_before prepared hooked_heap installed selected after source irq_prefix hook install restore ->
  let current := os_int_exit_installed_state transfer in
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_fragments) in
  exists (whole : kernel_c_sequence (kernel_program_environment_c_step env critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) initial first_heap input
    (orb (orb (orb prefix_stop false) suffix_stop) false) current after
    (coq_prop (flag_pend_call_endpoint_observations env sg (FlagPendTaskCaller original)
      original initial returned current) &&
     irq_selected_suffix_output env critical sg handler transfer original saved acquired receipt other frame)),
  kernel_program_environment_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ whole /\
  kernel_call_task_source returned current /\
  (receipt |-- active returned current).
Proof.
  intros environment critical sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed env active input prefix Hprefix Hprefix_idle bridge Hvalid Hdomain
    Hregistration Haddr Hresult Hparked Hcall Hnext Hrange Horiginal Hrunning Henabled.
  destruct (flag_task_rdy_next_outer_publication_prefix env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None initial first_heap input prefix_stop prefix_output entry before reference original
    pointer waiter old bits result c_result publication_local fragments pnode publication_frame middle published observed
    prefix Hprefix Hprefix_idle bridge Hvalid Hdomain Hregistration Haddr Hresult Hparked Hcall Hnext)
    as [post [schedule [publication [Hstep [Hpublication_source Hpublication_idle]]]]].
  pose proof (proj1 (kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ prefix)) as Hinput.
  destruct (flag_waiting_save_input_idle_non_idle env critical initial_local sg reference pointer original
    (armv7a_irq_fiq_mask saved) initial initial_private first_heap Hinput) as [Hidle Hnonidle].
  assert (Hsame_original : task_tcb_init_stack_same_call original reference).
  { destruct Hregistration as [task [[Hsame _] _]]; exact Hsame. }
  exists post, schedule; split; [exact Hstep|].
  intros suffix_stop suffix_output handler irq_entry transfer other frame irq_before prepared hooked_heap installed selected after
    source irq_prefix hook install restore receipt suffix suffix_bridge Hsuffix Hsuffix_idle complete current returned.
  pose (included := selected_publication_environment_sequence env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ suffix).
  pose (combined := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ publication (fun heap H => H) included).
  assert (Hcombined : kernel_program_environment_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ combined).
  { unfold combined; apply KernelCSourceThen; [exact Hpublication_source|].
    apply selected_publication_environment_sequence_source; exact Hsuffix. }
  assert (Hcombined_idle : flag_waiting_publication_prefix env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ combined).
  { unfold combined; apply FlagWaitingPrefixThen; [exact Hpublication_idle|].
    apply FlagWaitingPrefixSelected; exact Hsuffix_idle. }
  destruct (irq_published_completion_outer_sequence environment critical sg None handler irq_entry transfer original saved
    acquired receipt other frame irq_before prepared hooked_heap installed selected after source irq_prefix hook install restore
    initial first_heap input _ suffix_output combined suffix_bridge Hcombined Hcombined_idle Hrange Horiginal Hrunning
    Henabled complete) as [whole [Hwhole [Hwhole_idle [Hreturned Hstop]]]].
  destruct (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ whole))
    as [Hendpoint Howner].
  assert (Hsame_returned : task_tcb_init_stack_same_call returned reference).
  { destruct (proj1 (proj2 (proj2 (proj2 Hendpoint)))) as [Hsame Havailable].
    destruct Hsame as [Hi [Ho Hs]], Hsame_original as [Hi' [Ho' Hs']].
    repeat split; [exact (eq_trans Hi Hi')|exact (eq_trans Ho Ho')|exact (eq_trans Hs Hs')]. }
  pose proof (BuiltinComponent.os_int_exit_configured_transfer_hooked_eq environment sg handler irq_entry transfer source)
    as Hhooked.
  assert (Hreceipt : receipt |-- flag_pend_waiting_receipt sg reference pointer returned current).
  { eapply flag_waiting_published_terminal_receipt; [exact Hregistration|exact Hresult|exact Hstep|exact suffix| | |exact Hsame_returned|exact Hreturned];
      unfold current, os_int_exit_installed_state; rewrite Hhooked; reflexivity. }
  exists whole; split; [exact Hwhole|]. split; [exact Hreturned|].
  exact (flag_waiting_outer_endpoint_active env sg reference pointer original returned initial current receipt
    Horiginal Hsame_original Hendpoint Hidle Hnonidle Hreceipt).
Qed.

End FlagWaitingPublishedCalls.

Import FlagWaitingPublishedCalls FlagWaitingReceiptCaller.

Module FlagWaitingPublishedCaller.

(** A partial-correctness continuation for the two actual caller APIs.
    The saved word used to close the environment and the caller Restore
    saved word remain distinct.  All original caller/private heap joins
    and hardware transitions occur explicitly below. *)
Definition flag_waiting_caller_outputs (environment : TaskStackCallEnvironment) critical
  initial_local next_local initial_private active sg original closing_saved initial first_heap
  returned current restored : Prop :=
  (forall closing_arch
    (closing_restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical closing_arch)
    closing_cursor closing_written closing_middle closing_final environment_heap
    caller_heap private_before save_arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical save_arch)
    registers final_registers whole_after,
  closing_cursor.(kernel_restore_r0) = closing_saved ->
  armv7a_irq_fiq_mask closing_cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition closing_restore closing_cursor restored closing_written closing_middle ->
  armv7a_restore_suffix_transition closing_restore closing_written closing_middle closing_final environment_heap ->
  flag_pend_caller_save_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) initial caller_heap ->
  initial_private private_before -> join caller_heap private_before first_heap ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask closing_saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers current whole_after ->
  exists last_heap,
    CompletedCallerEvents.flag_pend_selected_caller_save_event environment critical initial_local active sg
      (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) final_registers.(kernel_save_r0) initial
      (FlagPendTaskCaller returned) returned current next_local caller_heap last_heap /\
    FlagPendActiveCaller.flag_pend_selected_caller_save_output environment critical initial_local active sg
      (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) initial caller_heap
      final_registers.(kernel_save_r0) last_heap) /\
  (forall closing_arch
    (closing_restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical closing_arch)
    closing_cursor closing_written closing_middle closing_final environment_heap
    outer_saved outer_acquired caller_heap private_before whole_before restore_arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical restore_arch)
    cursor written final_cursor whole_after,
  closing_cursor.(kernel_restore_r0) = closing_saved ->
  armv7a_irq_fiq_mask closing_cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition closing_restore closing_cursor restored closing_written closing_middle ->
  armv7a_restore_suffix_transition closing_restore closing_written closing_middle closing_final environment_heap ->
  armv7a_irq_fiq_mask outer_saved = armv7a_irq_fiq_mask closing_saved ->
  cursor.(kernel_restore_r0) = outer_saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical initial_local active sg
    (FlagPendTaskCaller original) original outer_saved outer_acquired initial caller_heap ->
  initial_private private_before -> join caller_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written first_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists last_heap,
    CompletedCallerEvents.flag_pend_selected_caller_restore_event environment critical initial_local active sg
      (FlagPendTaskCaller original) original outer_saved outer_acquired initial
      (FlagPendTaskCaller returned) returned current next_local caller_heap last_heap /\
    FlagPendActiveCaller.flag_pend_selected_caller_restore_output environment critical initial_local active sg
      (FlagPendTaskCaller original) original outer_saved outer_acquired initial caller_heap last_heap).

Lemma flag_waiting_return_caller_outputs :
  forall environment critical initial_local next_local initial_private active receipt frame sg original
    closing_saved closing_acquired initial first_heap stopped returned current restored
    (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      initial first_heap
      (flag_pend_caller_save_input environment critical initial_local active sg
        (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask closing_saved) initial ** initial_private)
      stopped current restored
      (coq_prop (flag_pend_call_endpoint_observations environment sg
        (FlagPendTaskCaller original) original initial returned current) &&
       flag_pend_caller_restore_input environment critical next_local (fun _ _ => receipt ** frame) sg
        (FlagPendTaskCaller returned) returned closing_saved closing_acquired current)),
  kernel_program_environment_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ run ->
  (receipt |-- active returned current) ->
  kernel_call_task_source returned current ->
  flag_waiting_caller_outputs environment critical initial_local next_local initial_private active sg original
    closing_saved initial first_heap returned current restored.
Proof.
  intros environment critical initial_local next_local initial_private active receipt frame sg original
    closing_saved closing_acquired initial first_heap stopped returned current restored run Hsource Hrecover Hreturned.
  unfold flag_waiting_caller_outputs; split; intros.
  - eapply FlagWaitingReceiptCaller.environment_receipt_save_active_output with (run := run); eassumption.
  - eapply FlagWaitingReceiptCaller.environment_receipt_restore_active_output with (run := run); eassumption.
Qed.

Lemma flag_task_rdy_next_task_caller_outputs :
  forall environment critical
    (task_abi : Armv7aTaskContextABI (task_sw_hook_call_environment environment).(task_stack_call_external)
      (task_sw_hook_call_environment environment).(task_stack_call_platform)
      (task_sw_hook_call_environment environment).(task_stack_call_port)
      (task_sw_hook_call_environment environment).(task_stack_call_continuations))
    sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed,
  let env := task_sw_hook_call_environment environment in
  let active := flag_pend_wait_active sg reference pointer in
  let input := flag_pend_caller_save_input env critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private in
  forall (prefix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input prefix_stop entry before prefix_output),
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  (prefix_output |-- flag_task_rdy_next_input env sg entry reference original pointer waiter old bits result
    publication_local pnode publication_frame) ->
  UCOS2_state_inv sg entry -> flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer original entry -> waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  exists post schedule,
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
  forall suffix_stop suffix_output frame other last_entry context saved_sp outgoing hooked incoming resumed
    (Hswitch : os_sched_requests_switch last_entry = true)
    (Hsave : env.(task_stack_call_external).(os_sched_arch_save_source) context saved_sp outgoing)
    (Hhook : kernel_client_step env.(task_stack_call_external).(os_sched_hook_action) sg
      (os_sched_save_current_sp (os_sched_prefix_state last_entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved_sp) hooked)
    (Hdestination : os_sched_destination_binding env.(task_stack_call_external)
      context outgoing hooked incoming resumed),
  let call := {| InstallComponent.task_install_fields_context := context;
                 InstallComponent.task_install_fields_outgoing := outgoing;
                 InstallComponent.task_install_fields_incoming := incoming;
                 InstallComponent.task_install_fields_resumed := resumed;
                 InstallComponent.task_install_fields_entry := hooked |} in
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  let local := kernel_sched_saved_local_resource_at env.(task_stack_call_platform)
    critical sg hooked.(TskState) original saved acquired receipt other in
  let rest := armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame in
  forall installed_heap installed sp actual
    (complete : InstallComponent.task_install_c_segment env local sg rest call installed_heap installed sp actual)
    (suffix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
      post published (flag_waiting_publication_owner env sg reference original pointer post publication_local
        pnode observed publication_frame) suffix_stop hooked installed_heap suffix_output),
  (suffix_output |-- InstallComponent.task_install_fields_entry_owner env local sg call ** rest) ->
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ suffix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ suffix ->
  incoming = original.(os_sched_call_stack) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  exists selected, forall restored,
  armv7a_task_restore_transition task_abi context selected installed restored ->
  let current := InstallComponent.task_install_fields_current call in
  let returned := kernel_selected_call selected current in
  flag_waiting_caller_outputs env critical initial_local other initial_private active sg original
    saved initial first_heap returned current restored.
Proof.
  intros environment critical task_abi sg reference original pointer initial first_heap initial_local initial_private
    saved acquired prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments
    pnode publication_frame middle published observed env active input prefix Hprefix Hprefix_idle bridge Hvalid Hdomain
    Hregistration Haddr Hresult Hparked Hcall Hnext Hrange Horiginal Hrunning Henabled.
  destruct (flag_task_rdy_next_task_return environment critical task_abi sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed prefix Hprefix Hprefix_idle bridge Hvalid Hdomain Hregistration Haddr
    Hresult Hparked Hcall Hnext Hrange Horiginal Hrunning Henabled)
    as [post [schedule [Hstep Hterminal]]].
  exists post, schedule; split; [exact Hstep|].
  intros suffix_stop suffix_output frame other last_entry context saved_sp outgoing hooked incoming resumed Hswitch Hsave
    Hhook Hdestination call receipt local rest installed_heap installed sp actual complete suffix suffix_bridge Hsuffix
    Hsuffix_idle Hincoming Hcoverage.
  destruct (Hterminal suffix_stop suffix_output frame other last_entry context saved_sp outgoing hooked incoming resumed
    Hswitch Hsave Hhook Hdestination installed_heap installed sp actual complete suffix suffix_bridge Hsuffix Hsuffix_idle
    Hincoming Hcoverage) as [selected Hcomplete].
  exists selected; intros restored Hrestore current returned.
  destruct (Hcomplete restored Hrestore) as [whole [Hwhole [Hreturned Hrecover]]].
  eapply flag_waiting_return_caller_outputs with (run := whole); eassumption.
Qed.

Lemma flag_task_rdy_next_irq_caller_outputs :
  forall environment critical sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed,
  let env := task_sw_hook_call_environment environment in
  let active := flag_pend_wait_active sg reference pointer in
  let input := flag_pend_caller_save_input env critical initial_local active sg
    (FlagPendTaskCaller original) original (armv7a_irq_fiq_mask saved) initial ** initial_private in
  forall (prefix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial first_heap input prefix_stop entry before prefix_output),
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix ->
  (prefix_output |-- flag_task_rdy_next_input env sg entry reference original pointer waiter old bits result
    publication_local pnode publication_frame) ->
  UCOS2_state_inv sg entry -> flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer original entry -> waiter.(flagNodeAddr) = pointer ->
  (result = PendOK \/ result = PendAbort) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer observed middle published ->
  task_in_range sg initial.(TskState) -> kernel_call_task_source original initial ->
  initial.(SchedState).(isRunning) = true -> os_sched_selection_enabled initial = true ->
  exists post schedule,
  flag_task_rdy sg entry pointer bits result = Some (schedule, post) /\
  forall suffix_stop suffix_output handler irq_entry transfer other frame irq_before prepared hooked_heap installed selected after
    source irq_prefix hook install restore,
  let receipt := flag_pend_waiting_receipt sg reference pointer original post in
  forall (suffix : kernel_c_sequence (kernel_program_selected_c_step env critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin))
    post published (flag_waiting_publication_owner env sg reference original pointer post publication_local
      pnode observed publication_frame) suffix_stop irq_entry irq_before suffix_output),
  (suffix_output |-- IRQCPrefix.os_int_exit_prefix_fields_owner env critical sg handler irq_entry original
    saved acquired receipt other frame) ->
  kernel_program_selected_c_sequence_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ suffix ->
  kernel_program_selected_sequence_idle_source env critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) _ _ _ _ _ _ _ suffix ->
  kernel_irq_acquired_c_completion environment critical sg handler irq_entry transfer original saved acquired receipt other frame
    irq_before prepared hooked_heap installed selected after source irq_prefix hook install restore ->
  let current := os_int_exit_installed_state transfer in
  let returned := kernel_restored_stack_call original transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_fragments) in
  flag_waiting_caller_outputs env critical initial_local other initial_private active sg original
    saved initial first_heap returned current after.
Proof.
  intros environment critical sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed env active input prefix Hprefix Hprefix_idle bridge Hvalid Hdomain
    Hregistration Haddr Hresult Hparked Hcall Hnext Hrange Horiginal Hrunning Henabled.
  destruct (flag_task_rdy_next_irq_return environment critical sg reference original pointer initial first_heap initial_local initial_private saved acquired
    prefix_stop prefix_output entry before waiter old bits result c_result publication_local fragments pnode
    publication_frame middle published observed prefix Hprefix Hprefix_idle bridge Hvalid Hdomain Hregistration Haddr
    Hresult Hparked Hcall Hnext Hrange Horiginal Hrunning Henabled)
    as [post [schedule [Hstep Hterminal]]].
  exists post, schedule; split; [exact Hstep|].
  intros suffix_stop suffix_output handler irq_entry transfer other frame irq_before prepared hooked_heap installed selected after
    source irq_prefix hook install restore receipt suffix suffix_bridge Hsuffix Hsuffix_idle complete current returned.
  destruct (Hterminal suffix_stop suffix_output handler irq_entry transfer other frame irq_before prepared hooked_heap installed
    selected after source irq_prefix hook install restore suffix suffix_bridge Hsuffix Hsuffix_idle complete)
    as [whole [Hwhole [Hreturned Hrecover]]].
  assert (Hclose :
    coq_prop (flag_pend_call_endpoint_observations env sg (FlagPendTaskCaller original) original initial returned current) &&
    irq_selected_suffix_output env critical sg handler transfer original saved acquired receipt other frame |--
    coq_prop (flag_pend_call_endpoint_observations env sg (FlagPendTaskCaller original) original initial returned current) &&
    flag_pend_caller_restore_input env critical other
      (fun _ _ => receipt ** (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame)) sg
      (FlagPendTaskCaller returned) returned saved acquired current).
  { unfold irq_selected_suffix_output, irq_selected_suffix_receipt,
      flag_pend_caller_restore_input, flag_pend_active_restore_input; Intros; entailer!. }
  pose proof (proj1 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ whole)) as Hinput.
  pose (adapted := KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hinput (fun heap H => H) whole Hclose).
  eapply flag_waiting_return_caller_outputs with (run := adapted).
  - apply KernelCSourceAdapt; exact Hwhole.
  - exact Hrecover.
  - exact Hreturned.

Qed.

End FlagWaitingPublishedCaller.
