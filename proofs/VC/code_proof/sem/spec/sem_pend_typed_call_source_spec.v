Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Logic.PropExtensionality.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.sched Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_receipt_producer_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_timeout_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_restore_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reduce only the opaque standard conjunction getter. This uses the
    existing propositional-extensionality boundary and changes no run. *)
Local Lemma sem_pend_typed_conjunction_second_eq : forall (P Q : Prop) (first : P) (second : Q),
  proj2 (conj first second) = second.
Proof.
  intros P Q first second.
  assert (Heq : Q = True).
  { apply propositional_extensionality; split; [intros; exact I|intros; exact second]. }
  revert first second; rewrite Heq; intros first second.
  destruct second; destruct (proj2 (conj first I)); reflexivity.
Qed.

(** The literal caller's arguments and its actual pre/post construct one
    original Wake segment. Both the receipt and returned owner refer to
    that same segment; no source trace is recovered from equal endpoints. *)
Lemma sem_pend_event_ready_typed_step :
  forall environment critical sg observer origin entry eid event slot old kind message result returned
    frame before after,
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  sem_pend_source_state_facts sg entry ->
  event_type_to_pend_type event.(eventType) = Some kind -> result <> PendTimeout ->
  (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** frame) before ->
  (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** frame) after ->
  exists segment : WakeComponent.kernel_wake_c_segment sg entry before
      (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** frame)
      (event_wake_state sg entry eid event slot old kind message result) after
      (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** frame),
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin _ _ _ _ _ _ segment) /\
    (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** frame) after.
Proof.
  intros environment critical sg observer origin entry eid event slot old kind message result returned frame
    before after Hlookup Hfacts Hkind Hresult Hpre Hpost.
  pose proof Hpre as [body [rest [Hjoin [[[Hentry Hbytes] Hbody] Hrest]]]].
  pose (segment := @WakeComponent.KernelWakeCEventSegment sg entry eid event slot old kind message result
    returned frame before after Hlookup Hentry Hpre Hpost).
  exists segment; split; [|exact Hpost].
  unfold segment; apply SemPendProgramWakeReceipt, SemPendWakeEventReceipt; assumption.
Qed.

(** The error branch performs no stores. Its own caller, tested owner and
    unchanged physical owner build the original critical segment. *)
Lemma sem_pend_mutex_post_not_owner_typed_step :
  forall environment critical source_env local sg observer origin frame context saved
    entry eid caller caller_node event mutex before,
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := entry;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := OS_ERR_NOT_MUTEX_OWNER;
    PostComponent.mutex_post_critical_schedule := false |} in
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) <> Some caller ->
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before before,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer origin source_env local frame call before before segment) /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call entry ** frame) before.
Proof.
  intros environment critical source_env local sg observer origin frame context saved
    entry eid caller caller_node event mutex before call Hlookup Htype Hfields Howner Hnative Hinput.
  pose (Hcritical := @mutex_post_not_owner sg eid caller entry event mutex Hlookup Htype Hfields Howner).
  pose (segment := @PostComponent.Build_mutex_post_critical_c_segment source_env
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical local sg frame call before before
    (conj Hnative Hcritical) Hinput Hinput).
  exists segment; split; [|exact Hinput].
  apply SemPendProgramMutexPostReceipt.
  unfold segment, call, PostComponent.mutex_post_critical_segment_source; cbn.
  rewrite sem_pend_typed_conjunction_second_eq.
  unfold Hcritical; apply SemPendMutexPostNotOwnerReceipt.
Qed.

(** The empty queue's actual count/pointer stores produce its endpoint
    owner. The preserved support remains indexed by the original caller
    and acquired entry; it is not converted to an observer's owner. *)
Lemma sem_pend_mutex_post_empty_typed_step :
  forall environment critical source_env local sg observer origin frame context saved
    entry eid caller caller_node event mutex prepared before prepared_heap after,
  let checkpoint := mutex_post_owner_state prepared eid event mutex None None in
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := checkpoint;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := OS_ERR_NONE;
    PostComponent.mutex_post_critical_schedule := false |} in
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller -> mutex_post_prepare sg mutex caller entry prepared ->
  encode_event_wait_grp event.(waitList) prepared.(TskState) = 0 ->
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call prepared ** frame) prepared_heap ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ prepared.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_empty_store_fragment sg eid prepared_heap after ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer origin source_env local frame call before after segment) /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg observer origin frame context saved
    entry eid caller caller_node event mutex prepared before prepared_heap after checkpoint call
    Hlookup Htype Hfields Howner Hprepare Hempty Hnative Hinput Hprepared Hslot Hstores.
  set (retained := critical_region_masked environment.(task_stack_call_platform) critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry ** unmap_table_rep sg **
    mutex_del_continuation_acquired source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) local sg context entry ** frame).
  assert (Hopen : PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call prepared ** frame |--
    coq_prop (UCOS2_state_inv sg prepared) && (UCOS2_inv sg prepared ** retained)).
  { unfold PostComponent.mutex_post_critical_c_owner, call, retained, UCOS2_inv; entailer!. }
  destruct (Hopen prepared_heap Hprepared) as [Hvalid Howned].
  assert (Hprepared_lookup : prepared.(EventState).(inUsedEventStates) eid = Some event).
  { rewrite (mutex_post_prepare_event_state_eq _ _ _ _ _ Hprepare); exact Hlookup. }
  pose proof (mutex_post_empty_fragment_preserves_resources sg prepared eid event mutex retained
    prepared_heap after Hvalid Hprepared_lookup Htype Hfields Hslot Hempty Howned Hstores) as Hwritten.
  assert (Hclose : UCOS2_inv sg checkpoint ** retained |--
    PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame).
  { unfold PostComponent.mutex_post_critical_c_owner, call, retained; entailer!. }
  pose proof (Hclose after Hwritten) as Houtput.
  pose (Hcritical := @mutex_post_empty sg eid caller entry event mutex prepared Hlookup Htype Hfields Howner Hprepare Hempty).
  pose (segment := @PostComponent.Build_mutex_post_critical_c_segment source_env
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical local sg frame call before after
    (conj Hnative Hcritical) Hinput Houtput).
  exists segment; split; [|exact Houtput].
  apply SemPendProgramMutexPostReceipt.
  unfold segment, call, PostComponent.mutex_post_critical_segment_source; cbn.
  rewrite sem_pend_typed_conjunction_second_eq.
  unfold Hcritical; apply SemPendMutexPostEmptyReceipt.
Qed.

(** The checked handover factory already consumes the actual EventReady
    post and subsequent stores. Specializing only its observation record
    exposes the same literal critical step to an arbitrary stored origin. *)
Lemma sem_pend_mutex_post_handover_typed_step :
  forall environment critical source_env local sg observer origin frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after,
  let wake := event_wake_state sg prepared eid event selected old PendMutex 0 PendOK in
  let found := event_set_wait_list event (remove_Z_eqb selected event.(waitList)) in
  let checkpoint := mutex_post_owner_state wake eid found mutex (Some selected) (Some priority) in
  let call := {| PostComponent.mutex_post_critical_context := context;
    PostComponent.mutex_post_critical_saved := saved;
    PostComponent.mutex_post_critical_entry := entry;
    PostComponent.mutex_post_critical_checkpoint := checkpoint;
    PostComponent.mutex_post_critical_eid := eid;
    PostComponent.mutex_post_critical_caller := caller;
    PostComponent.mutex_post_critical_node := caller_node;
    PostComponent.mutex_post_critical_result := mutex_post_handover_error sg mutex priority;
    PostComponent.mutex_post_critical_schedule := true |} in
  let retained := critical_region_masked environment.(task_stack_call_platform) critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
    mutex_del_continuation_acquired source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) local sg context entry ** frame in
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller -> mutex_post_prepare sg mutex caller entry prepared ->
  encode_event_wait_grp event.(waitList) prepared.(TskState) <> 0 ->
  mutex_post_native_caller sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    entry context caller caller_node ->
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call entry ** frame) before ->
  (UCOS2_inv sg prepared ** prepared_frame) prepared_heap ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ prepared.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  event_task_rdy_entry sg prepared.(TskState) eid event selected old ->
  ((event_task_rdy_post sg prepared.(TskState) eid event selected old 0 16 0
      (encode_ready_grp prepared.(SchedState).(readyList) prepared.(TskState))
      (sched_row_values prepared.(TskState) prepared.(SchedState).(readyList)) priority **
    mutex_del_wake_frame sg prepared eid selected) ** retained) helper_heap ->
  mutex_post_handover_store_fragment sg eid priority helper_heap after ->
  exists segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after,
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCMutexPost environment critical sg observer origin source_env local frame call before after segment) /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg observer origin frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after
    wake found checkpoint call retained Hlookup Htype Hfields Howner Hprepare Hnonempty Hnative Hinput
    Hprepared Hslot Hentry Hhelper Hstores.
  set (observed := {| os_sched_call_invocation := observer; os_sched_call_origin := origin;
    os_sched_call_stack := context.(os_sched_call_stack); os_sched_call_fragments := context.(os_sched_call_fragments) |}).
  destruct (sem_pend_mutex_post_handover_selected_source environment critical source_env local sg frame context
    saved entry eid caller caller_node event mutex prepared selected old priority prepared_heap prepared_frame
    before helper_heap after observed Hlookup Htype Hfields Howner Hprepare Hnonempty Hnative Hinput
    Hprepared Hslot Hentry Hhelper Hstores) as [segment [Hreceipt [_ [_ [_ Houtput]]]]].
  exists segment; exact (conj Hreceipt Houtput).
Qed.

(** This is an observation of the actual owned cut, including its active
    continuation and arbitrary frame. It supplies no future-step law. *)
Lemma sem_pend_event_ready_fields_typed_step :
  forall environment critical local active sg observer origin entry eid event slot old kind message result returned
    owner_frame call_frame before after,
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event_type_to_pend_type event.(eventType) = Some kind -> result <> PendTimeout ->
  (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
    local sg active entry ** owner_frame) before ->
  (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** call_frame) before ->
  (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** call_frame) after ->
  exists segment : WakeComponent.kernel_wake_c_segment sg entry before
      (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** call_frame)
      (event_wake_state sg entry eid event slot old kind message result) after
      (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** call_frame),
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin _ _ _ _ _ _ segment) /\
    (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** call_frame) after.
Proof.
  intros environment critical local active sg observer origin entry eid event slot old kind message result returned
    owner_frame call_frame before after Hlookup Hkind Hresult Howner Hpre Hpost.
  assert (Hopen : kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      local sg active entry ** owner_frame |-- coq_prop (UCOS2_state_inv sg entry) &&
    (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      local sg active entry ** owner_frame)).
  { unfold kernel_continuation_inv, kernel_program_fields_inv; entailer!. }
  eapply sem_pend_event_ready_typed_step; try eassumption.
  apply sem_pend_source_state_facts_from_valid; exact (proj1 (Hopen before Howner)).
Qed.

(** Stable, Lookup and Prepared keep their original phase invariants.
    In particular Prepared is not replaced by a stable ready invariant. *)
Lemma sem_pend_event_ready_delete_phase_typed_step :
  forall environment critical phase loan sg observer origin entry eid event slot old kind message result returned
    owner_frame call_frame before after,
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event_type_to_pend_type event.(eventType) = Some kind -> result <> PendTimeout ->
  (task_delete_phase_resources phase loan sg entry ** owner_frame) before ->
  (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** call_frame) before ->
  (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** call_frame) after ->
  exists segment : WakeComponent.kernel_wake_c_segment sg entry before
      (WakeComponent.event_ready_c_input sg entry eid event slot old kind result ** call_frame)
      (event_wake_state sg entry eid event slot old kind message result) after
      (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** call_frame),
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin _ _ _ _ _ _ segment) /\
    (WakeComponent.event_ready_c_output sg entry eid event slot old kind message result returned ** call_frame) after.
Proof.
  intros environment critical phase loan sg observer origin entry eid event slot old kind message result returned
    owner_frame call_frame before after Hlookup Hkind Hresult Howner Hpre Hpost.
  eapply sem_pend_event_ready_typed_step; try eassumption.
  eapply sem_pend_delete_phase_resources_facts; exact Howner.
Qed.

(** The Flag helper's existing post chooses its actual checkpoint and
    schedule bit. Keep those witnesses in the original Flag constructor. *)
Lemma sem_pend_flag_ready_typed_step :
  forall environment critical sg observer origin entry pointer waiter old bits result returned frame before after,
  task_flag_waiter_consistency sg entry.(TskState) entry.(FlagState) ->
  (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) before ->
  (flag_task_rdy_post sg entry pointer waiter bits result returned ** frame) after ->
  exists checkpoint (schedule : bool),
  exists segment : WakeComponent.kernel_wake_c_segment sg entry before
      (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) checkpoint after
      ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
        (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame),
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin _ _ _ _ _ _ segment) /\
    ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
      (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame) after.
Proof.
  intros environment critical sg observer origin entry pointer waiter old bits result returned frame before after
    Hconsistent Hpre [body [rest [Hjoin [[checkpoint [schedule [[Hsource [Hreturned Hvalid]] Hbody]]] Hrest]]]].
  assert (Hpost : ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
    (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame) after).
  { exists body, rest; split; [exact Hjoin|]. split; [split; [exact (conj Hreturned Hvalid)|exact Hbody]|exact Hrest]. }
  pose (segment := @WakeComponent.KernelWakeCFlagSegment sg entry pointer waiter old bits result returned
    schedule checkpoint frame before after Hpre Hsource Hpost).
  exists checkpoint, schedule, segment; split; [|exact Hpost].
  unfold segment; apply SemPendProgramWakeReceipt, SemPendWakeFlagReceipt; exact Hconsistent.
Qed.

(** Tick legitimately creates Timeout. Its checked concrete field merge
    supplies the actual successor owner; no non-Timeout test is imposed. *)
Lemma sem_pend_tick_task_typed_step :
  forall environment critical sg observer origin entry slot old frame before after,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false -> time_tick_lookup entry slot old ->
  (UCOS2_inv sg entry ** frame) before ->
  ((time_tick_body_cells sg slot (tick_task_update old)
      (time_tick_ready_group (tick_task_step sg slot old entry))
      (time_tick_ready_rows (tick_task_step sg slot old entry)) **
    time_tick_body_residual sg entry slot old) ** frame) after ->
  exists segment : WakeComponent.kernel_wake_c_segment sg entry before (UCOS2_inv sg entry ** frame)
      (tick_task_step sg slot old entry) after (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame),
    sem_pend_program_c_step_receipt environment critical sg observer origin _ _ _ _ _ _ _
      (@KernelProgramCWake environment critical sg observer origin _ _ _ _ _ _ segment) /\
    (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame) after.
Proof.
  intros environment critical sg observer origin entry slot old frame before after Hmulti Hlookup Hpre Hraw.
  pose proof Hpre as [body [rest [Hjoin [[Hvalid Hbody] Hrest]]]].
  assert (Hpost : (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame) after).
  { destruct Hraw as [out [outside [Hjoin' [Hbody' Hframe']]]].
    exists out, outside; split; [exact Hjoin'|]. split; [|exact Hframe'].
    exact (time_tick_body_merge_task_step__task_update_backedges sg entry slot old Hmulti Hvalid Hlookup out Hbody'). }
  pose (segment := @WakeComponent.KernelWakeCTickSegment sg entry slot old frame before after Hlookup Hpre Hpost).
  exists segment; split; [|exact Hpost].
  unfold segment; apply SemPendProgramWakeReceipt, SemPendWakeTickReceipt.
Qed.
