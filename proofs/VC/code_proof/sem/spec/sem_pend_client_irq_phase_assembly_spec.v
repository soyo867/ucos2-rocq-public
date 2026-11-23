Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_returned_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_control_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_c_call_envelope_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_wrapper_completion_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_completed_family_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_irq_module_assembly_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_module_assembly_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_irq_entry_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_client_annotation_spec.
Import UCOS2_C_Rules TaskStateDef.
Import SelectedReturnedCProgram SelectedReturnedCSource SelectedIRQWrapperCompletion OSIntExitReturnedC.
Import OSIntExitCCallControl OSIntExitCCallEnvelope OSIntExitCCallCompletion ReturnedIRQEntryResources ReturnedIRQCallSource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.
Import SelectedEnvironmentScopedPrimitives.
Import SelectedEnvironmentPhaseEffects SelectedEnvironmentPhaseProperties.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Section SemPendIRQPhaseAssembly.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (original : OsSchedCallContext).
Context (initial : UCOS2_Verify_State) (entry_node : TaskAbstractState)
  (handler : OsIntExitCallContext) (suspended : Armv7aContinuation) (publication : nat)
  (local : Armv7aContinuation -> Assertion) (receipt private_frame : Assertion)
  (before saved_heap body_heap : model).
Context (body_input : Assertion) (prefix_stop : bool) (observed : UCOS2_Verify_State)
  (read_heap : model) (prefix_output read_input : Assertion) (acquire_stop : bool)
  (entry : UCOS2_Verify_State) (acquired_heap : model) (acquire_output : Assertion).
Context (prefix : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin))
  (sem_pend_irq_entry_state initial handler suspended)
  body_heap body_input prefix_stop observed read_heap prefix_output).
Context (acquire : kernel_c_sequence (kernel_program_returned_c_step environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin))
  observed read_heap read_input acquire_stop entry acquired_heap acquire_output).
Context (observation_frame : Assertion) (node : TaskAbstractState) (middle after : model).
Context (Hentry : os_int_exit_first_level_entry_c_completion environment sg initial entry_node handler suspended
  publication (kernel_irq_fields_local local suspended receipt) (unmap_table_rep sg ** private_frame)
  before saved_heap body_heap).
Context (Hentry_bridge : os_int_exit_first_level_entry_output environment sg initial handler suspended
  (kernel_irq_fields_local local suspended receipt) (unmap_table_rep sg ** private_frame) |-- body_input).
Context (Hprefix_control : kernel_returned_c_body_sequence_source environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ prefix).
Context (Hread_bridge : prefix_output |-- read_input).
Context (Hacquire_control : kernel_returned_c_body_sequence_source environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin) _ _ _ _ _ _ _ acquire).
Context (Hreturn_bridge : acquire_output |--
  os_int_exit_returned_c_input environment sg entry local suspended receipt handler private_frame).
Context (Hreturned : os_int_exit_returned_c_completion environment critical sg observed read_heap observation_frame
  entry local suspended receipt original node handler private_frame acquired_heap middle after).

Let mask := handler.(os_int_exit_interrupted_mask).
Let private := task_stack_fragments_rep handler.(os_int_exit_handler_stack)
  handler.(os_int_exit_handler_fragments) ** private_frame.
Let caller_input := flag_pend_caller_save_input environment critical local (fun _ _ => receipt) sg
  (FlagPendTaskCaller original) original mask initial ** private.
Let parked := sem_pend_irq_entry_state initial handler suspended.
Let checkpoint := os_int_exit_ready_checkpoint observed.(SchedState).(isRunning) entry.
Let resumed := armv7a_continuation_resumed_call suspended original.
Let current := os_int_exit_wrapper_restored_state checkpoint suspended.(armv7a_continuation_stack).
Let completed := @OSIntExitFirstLevelCStep environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication (kernel_irq_fields_local local suspended receipt)
  (unmap_table_rep sg ** private_frame) before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire observation_frame local receipt original node private_frame middle after
  Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned.

Local Definition sem_pend_irq_actual_call : os_int_exit_first_level_c_call environment critical sg
  original.(os_sched_call_invocation) original.(os_sched_call_origin)
  initial entry_node handler suspended publication (kernel_irq_fields_local local suspended receipt)
  (unmap_table_rep sg ** private_frame) before saved_heap body_heap
  body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
  prefix acquire local receipt private_frame.
Proof. constructor; assumption. Defined.

(** The same terminal descriptor provides the live node. The original C
    lifetime proof determines its stopped bit; no future TaskSource is an input. *)
Lemma sem_pend_irq_actual_return_facts :
  UCOS2_state_inv sg initial -> kernel_call_task_source original initial ->
  orb prefix_stop (orb acquire_stop false) = false /\
  kernel_call_normal_return original initial resumed current /\
  kernel_call_task_source resumed current /\
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = mask.
Proof.
  intros Hvalid Htask.
  pose proof Htask as [Horigin [Hactive Hcurrent0]].
  pose proof (os_int_exit_returned_c_completion_wrapper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned)
    as Hwrapper.
  assert (Hstack : original.(os_sched_call_stack) = suspended.(armv7a_continuation_stack)).
  { pose proof (proj2 (irq_wrapper_c_binding _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper)) as Hbinding.
    rewrite (irq_wrapper_c_saved_call _ _ _ _ _ _ _ _ _ _ _ _ Hwrapper) in Hbinding; exact Hbinding. }
  assert (Hnormal : kernel_call_normal_return original initial resumed current).
  { eapply irq_wrapper_c_completion_normal_return; eassumption. }
  pose (tail := os_int_exit_first_level_c_tail environment critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    initial entry_node handler suspended publication (kernel_irq_fields_local local suspended receipt)
    (unmap_table_rep sg ** private_frame) before saved_heap body_heap
    body_input prefix_stop observed read_heap prefix_output read_input acquire_stop entry acquired_heap acquire_output
    prefix acquire observation_frame local receipt original node private_frame middle after Hreturned sem_pend_irq_actual_call).
  assert (Hrange : task_in_range sg parked.(TskState)).
  { pose proof (proj2 (os_int_exit_first_level_entry_c_resources _ _ _ _ _ _ _ _ _ _ _ _ Hentry)) as Howned.
    assert (Hopen : os_int_exit_first_level_entry_output environment sg initial handler suspended
      (kernel_irq_fields_local local suspended receipt) (unmap_table_rep sg ** private_frame) |--
      coq_prop (task_in_range sg parked.(TskState))).
    { unfold os_int_exit_first_level_entry_output, UCOS2_fields_inv; Intros.
      pose proof (proj1 (proj2 H)) as Hrange; entailer!. }
    exact (Hopen body_heap Howned). }
  assert (Hparked : task_invocation_active parked.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { eapply os_int_exit_first_level_entry_preserves_active; eassumption. }
  pose (returned_step := @OSIntExitReturnedCStep environment critical sg observed read_heap observation_frame
    entry local suspended receipt original node handler private_frame acquired_heap middle after Hreturned).
  destruct (os_int_exit_returned_c_step_task_fields _ _ _ _ _ _ _ _ _ _ returned_step)
    as [Hnodes [_ [Hcurrent Hpriority]]].
  assert (Horiginal : kernel_call_task_source original current).
  { eapply ReturnedLocalSource.kernel_program_returned_c_sequence_live_source_from_active with
      (initial := parked) (current := current) (node := node);
      [exact tail|exact Hrange|exact Horigin|exact Hparked| | |].
    - change (current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
      etransitivity; [exact Hcurrent|]. rewrite Hstack.
      exact (os_int_exit_returned_current _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned).
    - change (current.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node).
      etransitivity; [exact (f_equal (fun used => used original.(os_sched_call_stack).(stackLeaseSlot)) Hnodes)|].
      rewrite Hstack; exact (os_int_exit_returned_node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned).
    - rewrite Hstack; exact (os_int_exit_returned_generation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned). }
  assert (Hfinal : kernel_call_task_source resumed current).
  { unfold kernel_call_task_source, resumed, armv7a_continuation_resumed_call; cbn.
    rewrite <- Hstack; exact Horiginal. }
  assert (Hstop : orb prefix_stop (orb acquire_stop false) = false).
  { eapply kernel_call_completed_task_source_not_stopped;
      [exact (proj1 (proj2 Hvalid))|exact Htask| |exact Hnormal|exact Hfinal].
    exact (os_int_exit_first_level_c_step_observer_lifetime _ _ _ _ _ _ _ _ _ _ _ _ completed). }
  split; [exact Hstop|]. split; [exact Hnormal|]. split; [exact Hfinal|].
  destruct (armv7a_save_transition_observations _ _ _ environment.(task_stack_call_continuations)
    handler suspended before saved_heap (os_int_exit_entry_actual_save _ _ _ _ _ _ _ _ _ _ _ _ Hentry))
    as [_ [_ [_ [Hmask _]]]]. exact Hmask.
Qed.

(** This is the existing caller-local IRQ run, with its endpoint facts
    added by one Adapt. Its original prefix/acquire proofs and heaps are kept. *)
Lemma sem_pend_irq_scoped_module_run :
  forall prefix_origin acquired_origin,
  sem_pend_client_phase_context sg original initial -> os_sched_selection_enabled initial = true ->
  caller_input before ->
  kernel_program_returned_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    original.(os_sched_call_origin) parked prefix_stop prefix_origin observed ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    prefix_origin observed acquire_stop acquired_origin entry ->
  exists run : flag_pend_scoped_environment_run environment critical local local (fun _ _ => receipt) sg
    original mask initial before private false resumed current after private,
    sem_pend_client_module_run environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
      _ _ _ _ _ _ _ run original.(os_sched_call_origin) resumed.(os_sched_call_origin).
Proof.
  intros prefix_origin acquired_origin Hcontext Henabled Howned Hprefix_source Hacquire_source Hprefix_trace Hacquire_trace.
  destruct Hcontext as [Hvalid [Htask [Hrunning [Hidle [Havailable Hcache]]]]].
  pose proof (sem_pend_irq_actual_return_facts Hvalid Htask) as [Hstop [Hnormal [Hfinal Hmask]]].
  pose proof (proj1 Htask) as Horigin.
  destruct (sem_pend_irq_caller_local_module_run environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) initial entry_node handler suspended publication local receipt private_frame
    before saved_heap body_heap body_input prefix_stop observed read_heap prefix_output read_input acquire_stop
    entry acquired_heap acquire_output prefix acquire observation_frame original node middle after
    Hentry Hentry_bridge Hprefix_control Hread_bridge Hacquire_control Hreturn_bridge Hreturned Horigin
    original.(os_sched_call_origin) prefix_origin acquired_origin Howned Hprefix_source Hacquire_source
    Hprefix_trace Hacquire_trace) as [Hopen [Hclose [Hmodule Hafter]]].
  assert (Hreturned_origin : RunningInvocation suspended.(armv7a_continuation_stack).(stackLeaseSlot)
      suspended.(armv7a_continuation_stack).(stackLeaseGeneration) = resumed.(os_sched_call_origin)).
  { pose proof (os_int_exit_returned_binding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned) as [_ Hbinding].
    rewrite (os_int_exit_returned_saved_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hreturned) in Hbinding.
    unfold resumed; cbn [armv7a_continuation_resumed_call os_sched_call_origin]. rewrite Horigin, Hbinding; reflexivity. }
  destruct Hmodule as [Hsource Htrace]. rewrite Hreturned_origin in Htrace.
  assert (Htrace_return : sem_pend_client_return_source environment critical sg original initial resumed current).
  { split; [rewrite <- Hstop; exact Htrace|exact Hnormal]. }
  assert (Hendpoint : flag_pend_call_endpoint_observations environment sg (FlagPendTaskCaller original)
    original initial resumed current).
  { cbn [flag_pend_call_endpoint_observations].
    split.
    - eapply OSIntExitCCallReady.os_int_exit_first_level_c_step_conditional_ready;
        [exact completed|exact Henabled|exact Hnormal|exact Hfinal].
    - split.
      + intros [_ Hi].
        destruct (sem_pend_client_return_source_preserves_runtime environment critical sg original initial resumed current
          Htrace_return Hvalid Htask Hrunning (fun _ => Hi) Hcache) as [_ [Hr [Hidle' _]]]. exact (Hidle' Hr).
      + split.
        * intros [_ Hn].
          pose proof (sem_pend_task_client_return_preserves_non_idle environment critical sg original initial resumed
            current original Htrace_return Hvalid Hrunning Htask ltac:(unfold kernel_stack_call_same_call; repeat split; reflexivity) Hn)
            as Hn'.
          unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 (proj1 Hnormal))); exact Hn'.
        * split; [exact Hnormal|intro Hnotboot].
          exact (os_int_exit_first_level_c_step_control _ _ _ _ _ _ _ _ _ _ _ _ completed). }
  apply orb_false_iff in Hstop; destruct Hstop as [Hstop1 Hstop2].
  apply orb_false_iff in Hstop2; destruct Hstop2 as [Hstop2 _].
  subst prefix_stop acquire_stop; cbn in Hsource, Htrace.
  unfold kernel_program_environment_c_sequence_source in Hsource.
  lazymatch type of Hsource with
  | kernel_c_sequence_has_source ?segment ?atom_source ?state ?in_heap ?input
      false ?returned ?out_heap ?output ?actual =>
      pose (actual_run := actual); pose (actual_output := output)
  end.
  assert (Hfinish : actual_output |--
    coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original initial resumed current) &&
    (flag_pend_caller_save_input environment critical local (fun _ _ => receipt) sg
      (FlagPendTaskCaller resumed) resumed mask current ** private)).
  { intros heap Houtput; split; [exact Hendpoint|].
    rewrite <- Hmask. unfold private.
    change ((flag_pend_caller_save_input environment critical local (fun _ _ => receipt) sg
      (FlagPendTaskCaller resumed) resumed
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) current **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** private_frame) heap) in Houtput.
    destruct Houtput as [caller_handler [private_heap [Hjoin [Hcaller_handler Hprivate]]]].
    destruct Hcaller_handler as [caller_heap [handler_heap [Hcaller_join [Hcaller Hhandler]]]].
    destruct (join_assoc caller_heap handler_heap private_heap caller_handler heap Hcaller_join Hjoin)
      as [handler_private [Hprivate_join Hwhole_join]].
    exists caller_heap, handler_private; split; [exact Hwhole_join|].
    split; [exact Hcaller|]. exists handler_heap, private_heap.
    exact (conj Hprivate_join (conj Hhandler Hprivate)). }
  exists (KernelCSequenceAdapt
    (kernel_program_environment_c_step environment critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin))
    initial before caller_input caller_input false current after actual_output _
    Howned (fun heap Hinput => Hinput) actual_run Hfinish).
  split.
  - apply KernelCSourceAdapt; exact Hsource.
  - exact Htrace.
Qed.

(** The real Sem waiting Restore has already established enabled selection.
    The prefix below opens its actual masked input; the existing IRQ local
    bridge is then consumed immediately by the phase-producing CPU factory. *)
Lemma sem_pend_irq_waiting_restore_sched_input :
  forall waiting_original waiting_initial waiting_observed eid timeout waiting
    saved acquired first_heap private_before whole_before arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written final_cursor whole_after prefix_origin acquired_origin,
  sem_pend_client_sched_entry environment critical sg waiting_original mask waiting_initial waiting_observed
    eid timeout waiting original initial ->
  interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local (fun _ _ => receipt) sg
    (FlagPendTaskCaller original) original saved acquired initial first_heap ->
  private private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written before ->
  kernel_program_returned_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ prefix ->
  kernel_program_returned_c_sequence_source environment critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) None _ _ _ _ _ _ _ acquire ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    original.(os_sched_call_origin) parked prefix_stop prefix_origin observed ->
  sem_pend_observed_client_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None
    prefix_origin observed acquire_stop acquired_origin entry ->
  armv7a_restore_suffix_transition restore written after final_cursor whole_after ->
  exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local local
    (fun _ _ => receipt) sg original saved acquired initial first_heap false resumed current last_heap),
    ((coq_prop (sem_pend_client_return_source environment critical sg original initial resumed current /\
        kernel_call_control_rely sg initial current) &&
      sem_pend_client_sched_input environment local critical sg waiting_original mask waiting_initial
        waiting_observed eid timeout waiting resumed current) ** receipt) last_heap.
Proof.
  intros waiting_original waiting_initial waiting_observed eid timeout waiting saved acquired first_heap
    private_before whole_before arch restore cursor written final_cursor whole_after prefix_origin acquired_origin
    Hwaiting Hsaved Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hprefix_source Hacquire_source
    Hprefix_trace Hacquire_trace Hsuffix.
  assert (Hwhole : (flag_pend_caller_restore_input environment critical local (fun _ _ => receipt) sg
    (FlagPendTaskCaller original) original saved acquired initial ** private) whole_before).
  { exists first_heap, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (flag_pend_scoped_restore_prefix_sequence environment critical local (fun _ _ => receipt) sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) None original saved acquired initial
    private arch restore cursor whole_before written before Hr0 Hmask Hwhole Hprefix) as [actual_prefix Hprefix_source_actual].
  pose proof (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ actual_prefix)) as Hmiddle.
  rewrite (proj2 Hsaved) in Hmiddle.
  destruct (sem_pend_irq_scoped_module_run prefix_origin acquired_origin (proj1 Hwaiting)
    (proj1 (proj2 (proj2 Hwaiting))) Hmiddle Hprefix_source Hacquire_source Hprefix_trace Hacquire_trace)
    as [run Hmodule].
  (* Transport the chosen run and its indexed source together along the
     actual saved-mask equality, before applying the dependent consumer. *)
  assert (Hsaved_run : exists saved_run : flag_pend_scoped_environment_run
    environment critical local local (fun _ _ => receipt) sg original
    (armv7a_irq_fiq_mask saved) initial before private false resumed current after private,
    sem_pend_client_module_run environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) _ _ _ _ _ _ _ saved_run
      original.(os_sched_call_origin) resumed.(os_sched_call_origin)).
  { rewrite (proj2 Hsaved). exists run; exact Hmodule. }
  destruct Hsaved_run as [saved_run Hsaved_module].
  eapply sem_pend_module_waiting_restore_sched_input with
    (local := local) (next_local := local) (active := fun _ _ => receipt)
    (private_input := private) (private_output := private) (private_before := private_before)
    (whole_before := whole_before) (environment_heap := after) (restore := restore)
    (cursor := cursor) (written := written) (prefix_heap := before) (final_cursor := final_cursor)
    (whole_after := whole_after) (run := saved_run); eassumption.
Qed.

End SemPendIRQPhaseAssembly.
