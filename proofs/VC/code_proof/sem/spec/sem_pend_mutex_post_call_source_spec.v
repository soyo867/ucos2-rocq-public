Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_receipt_producer_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_typed_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The real factory retains this receipt before wrapping the same segment
    in a program step.  No inspection of a Prop-valued step is needed. *)
Lemma sem_pend_mutex_post_typed_observation :
  forall environment critical source_env local sg observer origin frame call before after
    (segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after),
  sem_pend_mutex_post_call_receipt environment critical source_env local sg frame call before after segment ->
  sem_pend_observed_client_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
    origin call.(PostComponent.mutex_post_critical_entry) false origin call.(PostComponent.mutex_post_critical_checkpoint).
Proof.
  intros environment critical source_env local sg observer origin frame call before after segment Hreceipt.
  eapply SemPendObservedMutexPost; try reflexivity; exact Hreceipt.
Qed.

Lemma sem_pend_mutex_post_call_certificate :
  forall environment critical source_env local sg observer stored_origin origin frame call before after
    (segment : PostComponent.mutex_post_critical_c_segment source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg frame call before after),
  let step := @KernelProgramCMutexPost environment critical sg observer stored_origin
    source_env local frame call before after segment in
  let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
  sem_pend_mutex_post_call_receipt environment critical source_env local sg frame call before after segment ->
  sem_pend_c_sequence_call_certificate _
    (fun state heap input stopped current output_heap output actual first last =>
      sem_pend_program_c_step_receipt environment critical sg observer stored_origin
        state heap input stopped current output_heap output actual /\
      sem_pend_observed_client_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
        first state stopped last current)
    _ _ _ _ _ _ _ run origin origin /\
  (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical local sg call call.(PostComponent.mutex_post_critical_checkpoint) ** frame) after.
Proof.
  intros environment critical source_env local sg observer stored_origin origin frame call before after segment step run Hreceipt.
  split.
  - apply SemPendCSequenceCallAtom; split.
    + apply SemPendProgramMutexPostReceipt; exact Hreceipt.
    + eapply sem_pend_mutex_post_typed_observation; exact Hreceipt.
  - exact (PostComponent.mutex_post_critical_segment_output _ _ _ _ _ _ _ _ _ _ segment).
Qed.

(** This real error branch performs no stores. The reflexive observation
    therefore describes this same call's actual endpoint and owner. It
    makes no claim about the distinct Prepare/commit branches. *)
Lemma sem_pend_mutex_post_not_owner_call_certificate :
  forall environment critical source_env local sg observer stored_origin origin
    frame context saved entry eid caller caller_node event mutex before,
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
    let step := @KernelProgramCMutexPost environment critical sg observer stored_origin
      source_env local frame call before before segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_c_sequence_call_certificate _
      (fun state heap input stopped current after output actual first last =>
        sem_pend_program_c_step_receipt environment critical sg observer stored_origin
          state heap input stopped current after output actual /\
        sem_pend_observed_client_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
          first state stopped last current)
      _ _ _ _ _ _ _ run origin origin /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call entry ** frame) before.
Proof.
  intros environment critical source_env local sg observer stored_origin origin
    frame context saved entry eid caller caller_node event mutex before call
    Hlookup Htype Hmutex Hnotowner Hcaller Hinput.
  destruct (sem_pend_mutex_post_not_owner_typed_step environment critical source_env local sg
    observer stored_origin frame context saved entry eid caller caller_node event mutex before
    Hlookup Htype Hmutex Hnotowner Hcaller Hinput) as [segment [Hreceipt Howner]].
  exists segment; cbn zeta; split; [|exact Howner].
  apply SemPendCSequenceCallAtom; split; [exact Hreceipt|].
  apply sem_pend_observed_client_trace_refl.
Qed.

(** This decoder consumes the checked empty factory on its original tuple. *)
Lemma sem_pend_mutex_post_empty_call_certificate :
  forall environment critical source_env local sg observer stored_origin origin frame context saved
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
    let step := @KernelProgramCMutexPost environment critical sg observer stored_origin
      source_env local frame call before after segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_c_sequence_call_certificate _
      (fun state heap input stopped current output_heap output actual first last =>
        sem_pend_program_c_step_receipt environment critical sg observer stored_origin
          state heap input stopped current output_heap output actual /\
        sem_pend_observed_client_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
          first state stopped last current)
      _ _ _ _ _ _ _ run origin origin /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg observer stored_origin origin frame context saved
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
  pose (Hcritical := @mutex_post_empty sg eid caller entry event mutex prepared
    Hlookup Htype Hfields Howner Hprepare Hempty).
  pose (segment := @PostComponent.Build_mutex_post_critical_c_segment source_env
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical local sg frame call before after
    (conj Hnative Hcritical) Hinput Houtput).
  assert (Hreceipt : sem_pend_mutex_post_call_receipt environment critical source_env local sg
    frame call before after segment).
  { unfold sem_pend_mutex_post_call_receipt, segment, call,
      PostComponent.mutex_post_critical_segment_source; cbn.
    rewrite sem_pend_typed_call_source_spec.sem_pend_typed_conjunction_second_eq.
    unfold Hcritical; apply SemPendMutexPostEmptyReceipt. }
  exists segment; apply sem_pend_mutex_post_call_certificate; exact Hreceipt.
Qed.

(** This decoder consumes the checked handover factory on its original tuple. *)
Lemma sem_pend_mutex_post_handover_call_certificate :
  forall environment critical source_env local sg observer stored_origin origin frame context saved entry eid caller caller_node
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
    let step := @KernelProgramCMutexPost environment critical sg observer stored_origin
      source_env local frame call before after segment in
    let run := KernelCSequenceAtom _ _ _ _ _ _ _ _ step in
    sem_pend_c_sequence_call_certificate _
      (fun state heap input stopped current output_heap output actual first last =>
        sem_pend_program_c_step_receipt environment critical sg observer stored_origin
          state heap input stopped current output_heap output actual /\
        sem_pend_observed_client_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg observer None
          first state stopped last current)
      _ _ _ _ _ _ _ run origin origin /\
    (PostComponent.mutex_post_critical_c_owner source_env environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical local sg call checkpoint ** frame) after.
Proof.
  intros environment critical source_env local sg observer stored_origin origin frame context saved entry eid caller caller_node
    event mutex prepared selected old priority prepared_heap prepared_frame before helper_heap after
    wake found checkpoint call retained Hlookup Htype Hfields Howner Hprepare Hnonempty Hnative Hinput
    Hprepared Hslot Hentry Hhelper Hstores.
  assert (Hvalid : UCOS2_state_inv sg prepared).
  { assert (Hopen : UCOS2_inv sg prepared ** prepared_frame |--
      coq_prop (UCOS2_state_inv sg prepared) && (UCOS2_inv sg prepared ** prepared_frame))
      by (unfold UCOS2_inv; entailer!).
    exact (proj1 (Hopen prepared_heap Hprepared)). }
  assert (Hprepared_lookup : prepared.(EventState).(inUsedEventStates) eid = Some event).
  { rewrite (mutex_post_prepare_event_state_eq _ _ _ _ _ Hprepare); exact Hlookup. }
  assert (Hreturn : priority = old.(curPrio)).
  { destruct Hhelper as [callee [rest [Hjoin [Hcore Hretained]]]].
    destruct Hcore as [owned [residual [Hjoin' [Hpost Hresidual]]]].
    exact (proj2 (proj1 Hpost)). }
  assert (Hwake : event_task_rdy sg prepared eid PendMutex 0 PendOK = Some (priority, wake)).
  { destruct Hhelper as [callee [rest [Hjoin [Hpost Hretained]]]].
    exact (proj1 (mutex_post_wake_merge_inv sg eid prepared event selected old priority
      Hvalid Hprepared_lookup Htype Hentry callee Hpost)). }
  assert (Hfound : wake.(EventState).(inUsedEventStates) eid = Some found).
  { unfold wake, found; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
      inUsedEventStates update_event_field_raw]; rewrite Z.eqb_refl; reflexivity. }
  pose proof (proj1 (mutex_post_wake_owner_selection sg prepared eid event selected old priority
    Hentry Hreturn)) as Htable.
  pose proof (sem_pend_mutex_post_handover_committed_owner environment critical source_env local sg frame
    context saved entry eid caller caller_node event mutex prepared selected old priority prepared_heap prepared_frame
    helper_heap after Hprepared Hprepared_lookup Htype Hfields Hslot Hentry Hhelper Hstores) as Houtput.
  destruct (sem_pend_mutex_post_handover_segment_receipt environment critical source_env local sg
    observer stored_origin frame context saved entry eid caller caller_node event mutex prepared priority wake found selected
    before after prepared_heap prepared_frame Hlookup Htype Hfields Howner Hprepare Hnonempty Hwake Hfound Htable
    Hnative Hinput Hprepared Houtput) as [segment [Hprogram_receipt Hsource]].
  assert (Hreceipt : sem_pend_mutex_post_call_receipt environment critical source_env local sg
    frame call before after segment).
  { unfold sem_pend_mutex_post_call_receipt, call, checkpoint; rewrite Hsource.
    apply sem_pend_mutex_post_handover_c_receipt; exact Hvalid. }
  exists segment; apply sem_pend_mutex_post_call_certificate; exact Hreceipt.
Qed.
