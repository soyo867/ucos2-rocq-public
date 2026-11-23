Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.tick Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_next_completion_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_dispatch_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_publication_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_fields_creation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_typed_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_sequence_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_module_assembly_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_registered_module_assembly_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Import KernelHeapObservation KernelHeapStorage SemPendEventReadySource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.
Import FlagTaskRdyNextCompletion.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual allocation factory creates both representations of its call
    once: the old heap-registry step and the original C Atom. The action is
    fixed by that allocation's entry invocation; no unrelated C step is
    paired with an endpoint-equal logical transition. *)
Lemma sem_pend_event_allocate_module :
  forall environment critical sg observer stored_origin origin actor state before (frame : Assertion),
  actor <> Some observer ->
  critical.(critical_region_clients)
    (event_create_allocate_client actor state.(EventState).(eventLifecycle).(eventNextInvocation)) ->
  sem_create_source_binding sg -> (kernel_program_fields_inv sg state ** frame) before ->
  exists result allocated after,
    let cut := match result with None => KernelClientHeapClosed
      | Some (eid, _) => KernelClientHeapExtra (event_pool_addr sg eid) end in
    let output := kernel_program_fields_inv sg allocated **
      (match result with None => emp | Some (eid, image) =>
        event_private_storage_rep sg eid (sem_create_allocation_identity state image) end) ** frame in
    kernel_client_heap_step mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after /\
    kernel_client_heap_state_step mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut allocated /\
    kernel_client_step (event_create_allocate_client actor
      state.(EventState).(eventLifecycle).(eventNextInvocation)) sg state allocated /\
    exists run : kernel_c_sequence (kernel_program_c_step environment critical sg observer stored_origin)
      state before (kernel_program_fields_inv sg state ** frame) false allocated after output,
      sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
        (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run)
        origin origin /\ output after.
Proof.
  intros environment critical sg observer stored_origin origin actor state before frame Hforeign Hmember Hbinding Hpre.
  destruct (sem_pend_event_allocate_fields_source sg state before frame Hbinding Hpre)
    as [result [allocated [after [Hread [Hcode [Hactual Hpost]]]]]].
  pose (segment := @EventCreationComponent.KernelEventCreationCAllocateFieldsSegment sg
    state result allocated before after frame Hread Hcode Hactual Hpre Hpost).
  pose (step := @KernelProgramCEventCreation environment critical sg observer stored_origin _ _ _ _ _ _ segment).
  pose (run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step).
  assert (Hcall : kernel_client_step (event_create_allocate_client actor
    state.(EventState).(eventLifecycle).(eventNextInvocation)) sg state allocated).
  { split; [reflexivity|]. exists result; exact Hcode. }
  assert (Htrace : sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
    origin state false origin allocated).
  { change false with (kernel_client_stops (event_create_allocate_client actor
      state.(EventState).(eventLifecycle).(eventNextInvocation)) observer).
    eapply sem_pend_nontimer_call_observed_source; [constructor|exact Hmember|exact Hforeign| |exact Hcall].
    intros; discriminate. }
  exists result, allocated, after; cbn zeta.
  split.
  - apply KernelClientHeapRegistered.
    destruct result as [[eid image]|].
    + destruct Hactual as [Hnonzero [next [Hnext Hwrite]]].
      eapply MutexDelCreatorHeapDetach; eassumption.
    + subst after; apply MutexDelCreatorHeapEmpty; assumption.
  - split.
    + apply KernelClientHeapExtraState; destruct result as [[eid image]|]; econstructor; exact Hcode.
    + split; [exact Hcall|]. exists run; split; [|exact Hpost].
      apply sem_pend_module_program_observation; [|exact Htrace].
      unfold run; apply KernelCSourceAtom; left; constructor.
      unfold segment; constructor; intros; discriminate.
Qed.

(** A single store factory covers the existing fields, rather than copying
    every creator API. Its returned run and model step use the same field,
    value, allocation and actual physical store execution. *)
Lemma sem_pend_event_store_module :
  forall environment critical sg observer stored_origin origin actor state eid allocation field value before
    (frame : Assertion),
  actor <> Some observer ->
  critical.(critical_region_clients) (event_create_private_store_client actor eid allocation field value) ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) -> event_create_field_value_in_range field value ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) before ->
  exists final after,
    let current := replace_EventS (event_private_write state.(EventState) eid allocation field (Some value)) state in
    kernel_heap_execution (event_create_field_writes (event_pool_addr sg eid) field value) before after /\
    kernel_client_step (event_create_private_store_client actor eid allocation field value) sg state current /\
    exists run : kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer stored_origin)
      state before (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)
      false current after (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg current ** frame),
      sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
        (sem_pend_module_selected_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
      (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg current ** frame) after.
Proof.
  intros environment critical sg observer stored_origin origin actor state eid allocation field value before frame
    Hforeign Hmember Hget Hfield Hrange Hpre.
  destruct (sem_pend_event_private_fields_sequence environment critical sg observer stored_origin
    state eid allocation field value before frame Hget Hfield Hrange Hpre)
    as [final [after [Hfinal [Hactual [run [Hsource Hreceipt]]]]]].
  assert (Hcall : kernel_client_step (event_create_private_store_client actor eid allocation field value) sg state
    (replace_EventS (event_private_write state.(EventState) eid allocation field (Some value)) state))
    by (split; [exact Hget|reflexivity]).
  exists final, after; cbn zeta; split; [exact Hactual|]. split; [exact Hcall|].
  exists run; split.
  - apply sem_pend_module_selected_observation; [exact Hsource|].
    change false with (kernel_client_stops (event_create_private_store_client actor eid allocation field value) observer).
    eapply sem_pend_nontimer_call_observed_source; [constructor|exact Hmember|exact Hforeign| |exact Hcall].
    intros; discriminate.
  - exact (proj2 (SelectedCProgram.kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)).
Qed.

Lemma sem_pend_event_publish_module :
  forall environment critical sg observer stored_origin origin actor state eid allocation node heap (frame : Assertion),
  actor <> Some observer ->
  critical.(critical_region_clients) (event_create_publication_client actor eid allocation node) ->
  UCOS2_state_inv sg state -> state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  (forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg state.(TskState) node field) ->
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = nil ->
  event_fields_consistency node -> event_payload_consistency sg node ->
  event_name_valid sg state.(NameState) node -> allocation.(eventPrivateMutexPCP) = None ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) heap ->
  let current := replace_EventS (event_publish state.(EventState) eid node) state in
  kernel_client_step (event_create_publication_client actor eid allocation node) sg state current /\
  exists run : kernel_c_sequence (SelectedCProgram.kernel_program_selected_c_step environment critical sg observer stored_origin)
    state heap (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)
    false current heap (kernel_program_fields_inv sg current ** frame),
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_selected_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
    (kernel_program_fields_inv sg current ** frame) heap.
Proof.
  intros environment critical sg observer stored_origin origin actor state eid allocation node heap frame
    Hforeign Hmember Hvalid Hget Hqueue Himage Hgeneration Hkind Hfields Hwait Hconsistent Hpayload Hname Hpcp Hpre current.
  destruct (sem_pend_event_publish_fields_sequence environment critical sg observer stored_origin state eid allocation
    node heap frame Hvalid Hget Hqueue Himage Hgeneration Hkind Hfields Hwait Hconsistent Hpayload Hname Hpcp Hpre)
    as [run [Hsource Hreceipt]].
  assert (Hcall : kernel_client_step (event_create_publication_client actor eid allocation node) sg state current)
    by (repeat split; assumption || reflexivity).
  split; [exact Hcall|]. exists run; split.
  - apply sem_pend_module_selected_observation; [exact Hsource|].
    change false with (kernel_client_stops (event_create_publication_client actor eid allocation node) observer).
    eapply sem_pend_nontimer_call_observed_source; [constructor|exact Hmember|exact Hforeign| |exact Hcall].
    intros; discriminate.
  - exact (proj2 (SelectedCProgram.kernel_program_selected_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ run)).
Qed.

(** The actual Flag post's EX is opened only once. Its operation equation
    is used both in the original segment and in the registered call step. *)
Lemma sem_pend_flag_ready_module :
  forall environment critical sg observer stored_origin origin actor entry pointer waiter old bits result returned
    frame before after,
  critical.(critical_region_clients) (flag_task_rdy_source_client actor pointer bits result) ->
  actor <> Some observer ->
  (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) before ->
  (flag_task_rdy_post sg entry pointer waiter bits result returned ** frame) after ->
  exists checkpoint (schedule : bool),
    let output := (coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
      (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame in
    kernel_client_step (flag_task_rdy_source_client actor pointer bits result) sg entry checkpoint /\
    exists segment : WakeComponent.kernel_wake_c_segment sg entry before
      (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) checkpoint after output,
      let run := KernelCSequenceAtom _ _ _ _ _ _ _ _
        (@KernelProgramCWake environment critical sg observer stored_origin _ _ _ _ _ _ segment) in
      sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
        (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
      output after.
Proof.
  intros environment critical sg observer stored_origin origin actor entry pointer waiter old bits result returned
    frame before after Hmember Hforeign Hpre
    [body [rest [Hjoin [[checkpoint [schedule [[Hsource [Hreturned Hvalid]] Hbody]]] Hrest]]]].
  assert (Hpost : ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
    (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame) after).
  { exists body, rest; split; [exact Hjoin|]. split; [split; [split; assumption|exact Hbody]|exact Hrest]. }
  pose (segment := @WakeComponent.KernelWakeCFlagSegment sg entry pointer waiter old bits result returned
    schedule checkpoint frame before after Hpre Hsource Hpost).
  assert (Hcall : kernel_client_step (flag_task_rdy_source_client actor pointer bits result) sg entry checkpoint)
    by (exists schedule; exact Hsource).
  exists checkpoint, schedule; cbn zeta; split; [exact Hcall|]. exists segment; cbn zeta; split; [|exact Hpost].
  apply sem_pend_module_program_observation; [apply KernelCSourceAtom; left; constructor|].
  change false with (kernel_client_stops (flag_task_rdy_source_client actor pointer bits result) observer).
  eapply sem_pend_registered_framed_call_observed_source; [exact Hmember|exact Hforeign| |exact Hcall| |].
  - intros; discriminate.
  - exact (proj1 (sem_pend_wake_source_current_timer_frame sg entry checkpoint
      (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ segment))).
  - apply TmrTaskCallFlagReady; exact Hcall.
Qed.

Lemma sem_pend_tick_task_module :
  forall environment critical sg observer stored_origin origin entry slot old frame before after,
  critical.(critical_region_clients) (time_tick_task_source_client slot old) ->
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false -> time_tick_lookup entry slot old ->
  (UCOS2_inv sg entry ** frame) before ->
  ((time_tick_body_cells sg slot (tick_task_update old)
      (time_tick_ready_group (tick_task_step sg slot old entry))
      (time_tick_ready_rows (tick_task_step sg slot old entry)) **
    time_tick_body_residual sg entry slot old) ** frame) after ->
  kernel_client_step (time_tick_task_source_client slot old) sg entry (tick_task_step sg slot old entry) /\
  exists segment : WakeComponent.kernel_wake_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    (tick_task_step sg slot old entry) after (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame),
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer stored_origin _ _ _ _ _ _ segment) in
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _
      (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ run) origin origin /\
    (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame) after.
Proof.
  intros environment critical sg observer stored_origin origin entry slot old frame before after
    Hmember Hmulti Hlookup Hpre Hraw.
  destruct (sem_pend_tick_task_typed_step environment critical sg observer stored_origin entry slot old frame
    before after Hmulti Hlookup Hpre Hraw) as [segment [Hreceipt Howned]].
  assert (Hcall : kernel_client_step (time_tick_task_source_client slot old) sg entry (tick_task_step sg slot old entry))
    by (split; [exact Hlookup|reflexivity]).
  split; [exact Hcall|]. exists segment; cbn zeta; split; [|exact Howned].
  apply sem_pend_module_program_observation; [apply KernelCSourceAtom; left; constructor|].
  change false with (kernel_client_stops (time_tick_task_source_client slot old) observer).
  eapply sem_pend_registered_framed_call_observed_source; [exact Hmember| | |exact Hcall| |].
  - discriminate.
  - intros; discriminate.
  - exact (proj1 (sem_pend_wake_source_current_timer_frame sg entry (tick_task_step sg slot old entry)
      (WakeComponent.kernel_wake_c_segment_source _ _ _ _ _ _ _ segment))).
  - apply TmrTaskCallTickTask; exact Hcall.
Qed.

Lemma sem_pend_flag_next_module :
  forall environment critical sg observer stored_origin origin actor entry reference call pointer waiter old bits result
    c_result local fragments pnode frame before middle after next,
  critical.(critical_region_clients) (flag_task_rdy_source_client actor pointer bits result) -> actor <> Some observer ->
  UCOS2_state_inv sg entry -> flag_task_rdy_domain sg entry pointer waiter old bits ->
  flag_active_waiting_registration reference pointer call entry -> waiter.(flagNodeAddr) = pointer ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key reference.(os_sched_call_stack)) =
    Some (reference.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg pointer bits result c_result before middle ->
  flag_source_next_assignment pnode pointer next middle after ->
  flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result local pnode frame before ->
  exists current schedule,
    kernel_client_step (flag_task_rdy_source_client actor pointer bits result) sg entry current /\
    exists segment : flag_task_rdy_next_c_segment environment sg entry before
      (flag_task_rdy_next_input environment sg entry reference call pointer waiter old bits result local pnode frame)
      false current after
      (flag_task_rdy_next_output environment sg current reference call pointer waiter bits result c_result
        schedule local pnode next frame),
      let run := KernelCSequenceAtom _ _ _ _ _ _ _ _
        (@KernelProgramEnvironmentFlagTaskRdyNext environment critical sg observer stored_origin _ _ _ _ _ _ _ segment) in
      sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _ run origin origin /\
      flag_task_rdy_next_output environment sg current reference call pointer waiter bits result c_result
        schedule local pnode next frame after.
Proof.
  intros environment critical sg observer stored_origin origin actor entry reference call pointer waiter old bits result
    c_result local fragments pnode frame before middle after next Hmember Hforeign Hvalid Hdomain Hregistration
    Haddr Hparked Hactual Hnext Hpre.
  destruct (flag_active_task_rdy_next_publish _ _ _ environment.(task_stack_call_continuations)
    sg entry reference call pointer waiter old bits result c_result local fragments pnode frame before middle after next
    Hvalid Hdomain Hregistration Haddr Hparked Hactual Hnext Hpre)
    as [current [schedule [Hstep [Hresult [Hnextvalue [Hnone Howned]]]]]].
  assert (Houtput : flag_task_rdy_next_output environment sg current reference call pointer waiter bits result
    c_result schedule local pnode next frame after).
  { split; [repeat split; assumption|exact Howned]. }
  pose (segment := @FlagTaskRdyNextCompletionCSegment environment sg entry reference call pointer waiter old bits result
    c_result local fragments pnode frame before middle after next schedule current
    Hvalid Hdomain Hregistration Haddr Hparked Hactual Hnext Hpre Hstep).
  assert (Hcall : kernel_client_step (flag_task_rdy_source_client actor pointer bits result) sg entry current)
    by (exists schedule; exact Hstep).
  exists current, schedule; split; [exact Hcall|]. exists segment; cbn zeta; split; [|exact Houtput].
  split; [apply KernelCSourceAtom; constructor|].
  change false with (kernel_client_stops (flag_task_rdy_source_client actor pointer bits result) observer).
  eapply sem_pend_registered_framed_call_observed_source; [exact Hmember|exact Hforeign| |exact Hcall| |].
  - intros; discriminate.
  - exact (proj1 (sem_pend_wake_source_current_timer_frame sg entry current
      (proj2 (flag_task_rdy_next_c_segment_source _ _ _ _ _ _ _ _ _ segment)))).
  - apply TmrTaskCallFlagReady; exact Hcall.
Qed.

(** This is a consequence for already produced calls, not an assumed
    Hmodules guarantee. The original heap step and state step, its C run,
    and the actual tail are combined at exactly the same middle heap. *)
Lemma sem_pend_registered_heap_trace_cons :
  forall Extra extra_step extra_effect environment critical sg observer stored_origin
    (cut middle_cut final_cut : KernelClientHeapCut Extra) before middle after
    (first_heap_step : kernel_client_heap_step extra_step sg cut before middle_cut middle)
    (tail : kernel_client_heap_trace extra_step sg middle_cut middle final_cut after)
    state transient current input middle_owner output first_origin middle_origin last_origin
    (first : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer stored_origin)
      state before input false transient middle middle_owner)
    (last : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer stored_origin)
      transient middle middle_owner false current after output),
  kernel_client_heap_state_step extra_effect sg cut state middle_cut transient ->
  kernel_client_heap_state_trace extra_effect sg middle_cut transient final_cut current ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _ first first_origin middle_origin ->
  sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _ last middle_origin last_origin ->
  kernel_client_heap_trace extra_step sg cut before final_cut after /\
  kernel_client_heap_state_trace extra_effect sg cut state final_cut current /\
  exists run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer stored_origin)
    state before input false current after output,
    sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _ run first_origin last_origin /\
    output after.
Proof.
  intros Extra extra_step extra_effect environment critical sg observer stored_origin cut middle_cut final_cut
    before middle after first_heap_step tail state transient current input middle_owner output first_origin
    middle_origin last_origin first last Hstep Htail Hfirst Hlast.
  split; [exact (KernelClientHeapTraceCons _ _ _ _ _ _ _ _ first_heap_step tail)|].
  split; [econstructor; eassumption|].
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ first (fun h H => H) last).
  split.
  - exact (sem_pend_client_module_then environment critical sg observer stored_origin state before input false
      transient middle middle_owner middle_owner false current after output first (fun h H => H) last
      first_origin middle_origin last_origin Hfirst Hlast).
  - exact (proj2 (kernel_program_environment_c_sequence_resources _ _ _ _ _ _ _ _ _ _ _ _ last)).
Qed.

(** A real instance of the heap aggregation above. Both allocation return
    branches construct their old heap-registry step in the actual supplier;
    the same result is consumed here, without an observation assumption. *)
Lemma sem_pend_event_allocate_heap_trace :
  forall environment critical sg observer stored_origin origin actor state before (frame : Assertion),
  actor <> Some observer ->
  critical.(critical_region_clients)
    (event_create_allocate_client actor state.(EventState).(eventLifecycle).(eventNextInvocation)) ->
  sem_create_source_binding sg -> (kernel_program_fields_inv sg state ** frame) before ->
  exists result allocated after,
    let cut := match result with None => KernelClientHeapClosed
      | Some (eid, _) => KernelClientHeapExtra (event_pool_addr sg eid) end in
    let output := kernel_program_fields_inv sg allocated **
      (match result with None => emp | Some (eid, image) =>
        event_private_storage_rep sg eid (sem_create_allocation_identity state image) end) ** frame in
    kernel_client_heap_trace mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after /\
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut allocated /\
    exists run : kernel_c_sequence (kernel_program_environment_c_step environment critical sg observer stored_origin)
      state before (kernel_program_fields_inv sg state ** frame) false allocated after output,
      sem_pend_client_module_run environment critical sg observer stored_origin _ _ _ _ _ _ _ run origin origin /\ output after.
Proof.
  intros environment critical sg observer stored_origin origin actor state before frame Hforeign Hmember Hbinding Hpre.
  destruct (sem_pend_event_allocate_module environment critical sg observer stored_origin origin actor state before frame
    Hforeign Hmember Hbinding Hpre) as [result [allocated [after [Hheap [Hstep [Hcall [first [Hfirst Howned]]]]]]]].
  exists result, allocated, after; cbn zeta in *.
  eapply (sem_pend_registered_heap_trace_cons _ _ _ environment critical sg observer stored_origin
    _ _ _ before after after Hheap (KernelClientHeapTraceNil _ _ _ after)
    state allocated allocated _ _ _ origin origin origin
    (sem_pend_module_program_sequence environment critical sg observer stored_origin _ _ _ _ _ _ _ first)
    (KernelCSequenceRefl _ _ _ _ Howned)).
  - exact Hstep.
  - constructor.
  - exact Hfirst.
  - apply sem_pend_client_module_refl.
Qed.
