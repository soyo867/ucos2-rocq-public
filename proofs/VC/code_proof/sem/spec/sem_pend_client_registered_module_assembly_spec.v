Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait Ucos2Verify.lib.sched Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_receipt_producer_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_sequence_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_call_connection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_module_assembly_spec.
Import UCOS2_C_Rules TaskStateDef.
Import BuiltinComponent.
Import SemPendEventReadySource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** At this actual Extra supplier, retain the aggregate's Hstep and Hmiddle
    beside the C run before the old resource-guarantee codomain hides them.
    The helper's deterministic result identifies the aggregate's single EX
    state with the actual Wake endpoint. No run is replaced by another run. *)
Lemma sem_pend_module_registered_sem_post :
  forall environment critical local sg observer stored_origin origin request entry node result before after
    (frame : Assertion),
  critical.(critical_region_clients)
    (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event)) ->
  request.(sem_pend_fields_post_actor) <> observer ->
  sem_post_lookup entry request.(sem_pend_fields_post_event) node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg request.(sem_pend_fields_post_event) ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg request.(sem_pend_fields_post_event)) result before after ->
  kernel_client_heap_step sem_pend_fields_post_heap_execution sg
    (KernelClientHeapExtra request) before KernelClientHeapClosed after /\
  exists current (run : kernel_c_sequence (kernel_program_c_step environment critical sg observer stored_origin)
    entry before
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame)
    false current after
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg current ** frame)),
    kernel_client_heap_state_step sem_pend_fields_post_heap_effect sg
      (KernelClientHeapExtra request) entry KernelClientHeapClosed current /\
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run)
      origin origin /\
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg current ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin origin request entry node result before after frame
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual.
  set (abi := environment.(task_stack_call_continuations)).
  set (event := request.(sem_pend_fields_post_event)).
  set (stacks := store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks)).
  assert (Hopen : kernel_client_continuation_fields_world abi local sg entry ** frame |--
    coq_prop (UCOS2_state_inv sg entry /\ task_stack_live_coverage entry.(TskState) None) &&
    (kernel_program_fields_inv sg entry ** stacks ** frame)).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv, kernel_program_fields_inv, stacks;
      entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Hworld].
  assert (Hsplit : kernel_program_fields_inv sg entry ** stacks ** frame |--
    EX selected old, coq_prop (event_task_rdy_entry sg entry.(TskState) event node selected old) &&
      (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK **
        (sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame))).
  { rewrite kernel_program_fields_inv_split_unmap.
    sep_apply_l_atomic (sem_pend_event_ready_fields_split sg entry event node Hvalid Hlookup Htype Hgroup Hlayout).
    Intros selected old; Exists selected old; entailer!. }
  destruct (Hsplit before Hworld) as [selected [old [Hentry Howned]]].
  set (residual := sem_pend_event_ready_fields_frame sg entry event selected ** stacks ** frame).
  assert (Hselected : kernel_client_continuation_fields_world abi local sg entry ** frame |--
      WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual).
  { intros heap Hheap.
    destruct (Hopen heap Hheap) as [_ Hresources].
    destruct (Hsplit heap Hresources) as [other [previous [Hother Hraw]]].
    destruct (sem_pend_event_ready_entry_unique sg entry.(TskState) event node selected old other previous
      Hentry Hother) as [-> ->].
    exact Hraw. }
  pose proof (sem_post_waiter_source_post sg entry.(TskState) event node selected old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) result before after residual
    Howned Hactual) as Hpost.
  set (wake := event_wake_state sg entry event node selected old PendSem 0 PendOK).
  assert (Hclose : WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK result **
      residual |-- kernel_client_continuation_fields_world abi local sg wake ** frame).
  { pose proof (sem_pend_event_ready_fields_merge_continuations environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) abi sg entry event node
      selected old result local None Hvalid Hlookup Htype Hentry Hcoverage) as Hjoin.
    cbn zeta in Hjoin; unfold residual, stacks, wake; sepcon_assoc_change; sep_apply_l_atomic Hjoin.
    unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
  destruct (sem_pend_sem_post_module_call_output environment critical local sg observer origin request entry node
    result before after frame Hmember Hforeign Hlookup Htype Hgroup Hlayout Hpre Hactual)
    as [Hheap [current [Hstep [[priority Hwake] [Htrace Hmiddle]]]]].
  assert (Hhelper : event_task_rdy sg entry event PendSem 0 PendOK = Some (old.(curPrio), wake)).
  { unfold wake; eapply WakeComponent.event_task_rdy_c_entry_source; eassumption. }
  assert (Hcurrent : current = wake).
  { unfold sem_post_wake_result in Hwake; unfold event in Hhelper; congruence. }
  subst current.
  pose (body := @WakeComponent.KernelWakeCEventSegment sg entry event node selected old PendSem 0 PendOK
    result residual before after Hlookup Hentry Howned Hpost).
  pose (step := @KernelProgramCWake environment critical sg observer stored_origin _ _ _ _ _ _ body).
  pose (atom := @KernelCSequenceAtom (kernel_program_c_step environment critical sg observer stored_origin)
    _ _ _ _ _ _ _ step).
  pose (run := @KernelCSequenceAdapt (kernel_program_c_step environment critical sg observer stored_origin)
    entry before (kernel_client_continuation_fields_world abi local sg entry ** frame)
    (WakeComponent.event_ready_c_input sg entry event node selected old PendSem PendOK ** residual)
    false wake after
    (WakeComponent.event_ready_c_output sg entry event node selected old PendSem 0 PendOK result ** residual)
    (kernel_client_continuation_fields_world abi local sg wake ** frame) Hpre Hselected atom Hclose).
  split; [exact Hheap|]. exists wake, run.
  split; [exact Hstep|]. split; [|exact Hmiddle].
  apply sem_pend_module_program_observation; [|exact Htrace].
  unfold run; apply KernelCSourceAdapt.
  unfold atom; apply KernelCSourceAtom; left; constructor.
Qed.

(** The two builtin suppliers already return the actual C completion and
    physical endpoints. Their registered observations are consequences of
    those completions, not decoders assumed for an arbitrary raw Atom. *)
Lemma sem_pend_module_counter_completion :
  forall environment critical local sg observer stored_origin origin operation state frame before after code
    (completed : kernel_counter_c_completion operation sg state frame before after code),
  critical.(critical_region_clients)
    (kernel_full_profile_cut_client
      (match operation with KernelCounterCEnter => KernelFullIntEnter
       | KernelCounterCExit running => KernelFullIntExitCounter running end)) ->
  let segment := KernelBuiltinCCounter environment critical local sg operation state frame before after code completed in
  let step := @KernelProgramCBuiltin environment critical sg observer stored_origin local _ _ _ _ _ _ segment in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
  (UCOS2_fields_raw_rep sg state ** frame) before /\
  (UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin origin operation state frame before after code
    completed Hmember; cbn zeta.
  destruct (sem_pend_counter_c_completion_observed_source environment critical sg observer origin operation
    state frame before after code completed Hmember) as [Htrace Howned].
  split; [|exact Howned].
  apply sem_pend_module_program_observation; [|exact Htrace].
  apply KernelCSourceAtom; right; constructor; constructor.
Qed.

Lemma sem_pend_module_publication_completion :
  forall environment critical local sg observer stored_origin origin publication state frame before after code effect
    (completed : kernel_publication_c_completion environment.(task_stack_call_continuations) local sg
      publication state frame before after code effect),
  critical.(critical_region_clients) (task_create_stack_publication_client publication) ->
  publication.(stack_publication_invocation) <> observer ->
  let segment := KernelBuiltinCPublication environment critical local sg publication state frame before after
    code effect completed in
  let step := @KernelProgramCBuiltin environment critical sg observer stored_origin local _ _ _ _ _ _ segment in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
  (kernel_client_continuation_fields_publication environment.(task_stack_call_continuations) local sg
    publication state ** frame) before /\
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
    (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin origin publication state frame before after code
    effect completed Hmember Hforeign; cbn zeta.
  destruct (sem_pend_publication_c_completion_observed_source environment critical local sg observer origin
    publication state frame before after code effect completed Hmember Hforeign) as [Htrace Howned].
  split; [|exact Howned].
  apply sem_pend_module_program_observation; [|exact Htrace].
  apply KernelCSourceAtom; right; constructor; constructor; exact Hforeign.
Qed.

Lemma sem_pend_module_registered_event_ready :
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
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
    (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** frame) after.
Proof.
  intros environment critical sg observer stored_origin origin actor entry eid event slot old kind message result returned
    frame before after Hmember Hforeign Hlookup Hfacts Hkind Hresult Hpre Hpost.
  destruct (sem_pend_event_ready_c_call_certificate environment critical sg observer stored_origin origin actor
    entry eid event slot old kind message result returned frame before after
    Hmember Hforeign Hlookup Hfacts Hkind Hresult Hpre Hpost) as [segment [Hcalls Howned]].
  exists segment; cbn zeta; split; [|exact Howned].
  apply sem_pend_module_program_certificate; [|exact Hcalls].
  apply KernelCSourceAtom; left; constructor.
Qed.

(** A concrete aggregation step: use the prefix's actual output on the
    middle heap to call SemPost, then keep that same Hstep/Hmiddle and append
    its returned run. The result is directly the run packet consumed by the
    existing Save, final Restore and waiting Restore phase producers. *)
Lemma sem_pend_module_registered_sem_post_append :
  forall environment critical local sg observer stored_origin first_origin origin
    state before input stopped entry middle prefix_output
    (prefix : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer stored_origin)
      state before input stopped entry middle prefix_output)
    request node result after (frame : Assertion),
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _ prefix first_origin origin ->
  prefix_output |-- kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg entry ** frame ->
  critical.(critical_region_clients)
    (sem_pend_post_source_client request.(sem_pend_fields_post_actor) request.(sem_pend_fields_post_event)) ->
  request.(sem_pend_fields_post_actor) <> observer ->
  sem_post_lookup entry request.(sem_pend_fields_post_event) node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg request.(sem_pend_fields_post_event) ->
  sem_post_waiter_execution sg (event_addr sg request.(sem_pend_fields_post_event)) result middle after ->
  kernel_client_heap_step sem_pend_fields_post_heap_execution sg
    (KernelClientHeapExtra request) middle KernelClientHeapClosed after /\
  exists current (run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer stored_origin)
    state before input (stopped || false) current after
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg current ** frame)),
    kernel_client_heap_state_step sem_pend_fields_post_heap_effect sg
      (KernelClientHeapExtra request) entry KernelClientHeapClosed current /\
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _ run first_origin origin /\
    (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg current ** frame) after.
Proof.
  intros environment critical local sg observer stored_origin first_origin origin state before input stopped
    entry middle prefix_output prefix request node result after frame Hprefix Hbridge
    Hmember Hforeign Hlookup Htype Hgroup Hlayout Hactual.
  pose proof (proj2 (kernel_program_environment_c_sequence_resources environment critical sg observer stored_origin
    _ _ _ _ _ _ _ prefix)) as Hmiddle.
  destruct (sem_pend_module_registered_sem_post environment critical local sg observer stored_origin origin request
    entry node result middle after frame Hmember Hforeign Hlookup Htype Hgroup Hlayout
    (Hbridge middle Hmiddle) Hactual) as [Hheap [current [last [Hstep [Hlast Howned]]]]].
  split; [exact Hheap|].
  exists current, (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ prefix Hbridge
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ last)).
  split; [exact Hstep|]. split; [|exact Howned].
  eapply sem_pend_client_module_then with (transient := origin); eassumption.
Qed.
