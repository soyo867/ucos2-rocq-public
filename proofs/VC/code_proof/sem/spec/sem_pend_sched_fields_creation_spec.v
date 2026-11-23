Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_dispatch_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_publication_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_task_prepare_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_module_c_sequence_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Import KernelHeapObservation KernelHeapStorage.
Import SelectedReturnPrimitive SelectedCompletionSource SelectedCProgram SelectedCSource.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The lower fields alternatives enter the original selected language.
    Every certificate is indexed by the very atom being constructed. *)
Lemma sem_pend_event_creation_selected_sequence :
  forall environment critical sg observer origin event_observer state before input current after output
    (segment : EventCreationComponent.kernel_event_creation_c_segment sg state before input current after output),
  kernel_event_creation_c_segment_source sg event_observer _ _ _ _ _ _ segment ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input false current after output,
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin event_observer state before input current after output segment Hsource.
  set (original := @KernelProgramCEventCreation environment critical sg observer origin
    state before input current after output segment).
  set (returned := @KernelProgramReturnOriginal environment critical sg observer origin
    state before input false current after output original).
  set (selected := @KernelSelectedProgramReturn critical sg observer origin environment
    state before input false current after output returned).
  exists (KernelCSequenceAtom _ state before input false current after output selected).
  split; apply KernelCSourceAtom; unfold selected, returned, original.
  - apply KernelSelectedProgramReturnSource, KernelProgramReturnOriginalSource.
    left; apply KernelProgramCEventCreationSource; exact Hsource.
  - apply SemPendSelectedReturnReceipt, SemPendReturnOriginalReceipt, SemPendProgramEventCreationReceipt.
Qed.

Lemma sem_pend_task_creation_selected_sequence :
  forall environment critical sg observer origin event_observer state before input current after output
    (segment : CreationComponent.kernel_task_creation_c_segment sg state before input current after output),
  kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _ segment ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input false current after output,
    kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
      _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin event_observer state before input current after output segment Hsource.
  set (original := @KernelProgramCTaskCreation environment critical sg observer origin
    state before input current after output segment).
  set (returned := @KernelProgramReturnOriginal environment critical sg observer origin
    state before input false current after output original).
  set (selected := @KernelSelectedProgramReturn critical sg observer origin environment
    state before input false current after output returned).
  exists (KernelCSequenceAtom _ state before input false current after output selected).
  split; apply KernelCSourceAtom; unfold selected, returned, original.
  - apply KernelSelectedProgramReturnSource, KernelProgramReturnOriginalSource.
    left; apply KernelProgramCTaskCreationSource; exact Hsource.
  - apply SemPendSelectedReturnReceipt, SemPendReturnOriginalReceipt, SemPendProgramTaskCreationReceipt.
Qed.

Lemma sem_pend_event_allocate_fields_sequence :
  forall environment critical sg observer origin state before (frame : Assertion),
  sem_create_source_binding sg -> (kernel_program_fields_inv sg state ** frame) before ->
  exists result allocated after,
    event_create_allocate_critical state result allocated /\
    exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before (kernel_program_fields_inv sg state ** frame) false allocated after
      (kernel_program_fields_inv sg allocated **
       (match result with None => emp | Some (eid, image) =>
          event_private_storage_rep sg eid (sem_create_allocation_identity state image) end) ** frame),
      kernel_program_selected_c_sequence_source environment critical sg observer origin None _ _ _ _ _ _ _ run /\
      sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin state before frame Hbinding Hpre.
  destruct (sem_pend_event_allocate_fields_source sg state before frame Hbinding Hpre)
    as [result [allocated [after [Hread [Hcode [Hrun Hpost]]]]]].
  set (segment := @EventCreationComponent.KernelEventCreationCAllocateFieldsSegment sg
    state result allocated before after frame Hread Hcode Hrun Hpre Hpost).
  assert (Hsource : kernel_event_creation_c_segment_source sg None _ _ _ _ _ _ segment).
  { unfold segment; constructor; intros; discriminate. }
  exists result, allocated, after; split; [exact Hcode|].
  exact (sem_pend_event_creation_selected_sequence environment critical sg observer origin None
    _ _ _ _ _ _ segment Hsource).
Qed.

Lemma sem_pend_event_private_fields_sequence :
  forall environment critical sg observer origin state eid allocation field stored before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_create_field_value_in_range field stored ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) before ->
  exists final after,
    (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
      eid = Some final /\
    kernel_heap_execution (event_create_field_writes (event_pool_addr sg eid) field stored) before after /\
    exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)
      false (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) after
      (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg
        (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame),
      kernel_program_selected_c_sequence_source environment critical sg observer origin None _ _ _ _ _ _ _ run /\
      sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin state eid allocation field stored before frame Hget Hfield Hrange Hpre.
  destruct (sem_pend_private_field_fields_resources sg state eid allocation field stored before frame
    Hget Hfield Hrange Hpre) as [final [after [Hfinal [Hrun Hpost]]]].
  set (segment := @EventCreationComponent.KernelEventCreationCStoreFieldsSegment sg state eid allocation
    field stored final before after frame Hget Hfield Hfinal Hrun Hpre Hpost).
  assert (Hsource : kernel_event_creation_c_segment_source sg None _ _ _ _ _ _ segment).
  { unfold segment; constructor; intros; discriminate. }
  exists final, after; split; [exact Hfinal|]. split; [exact Hrun|].
  exact (sem_pend_event_creation_selected_sequence environment critical sg observer origin None
    _ _ _ _ _ _ segment Hsource).
Qed.

(** Build the finite store sequence while its actual middle heap and owner
    still exist. An aggregate endpoint is never used to choose new cuts. *)
Lemma sem_pend_event_private_prefix_fields_sequence :
  forall environment critical sg observer origin eid writes state allocation before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  Forall (fun write => In (fst write) (event_fields sg.(osKernelConfig).(cfgEventNames)) /\
    event_create_field_value_in_range (fst write) (snd write)) writes ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) before ->
  exists final current after,
    event_create_private_stores eid writes state tt current /\
    current.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes (event_pool_addr sg eid) (fst write) (snd write)) writes)
      before after /\
    exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)
      false current after (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg current ** frame),
      kernel_program_selected_c_sequence_source environment critical sg observer origin None _ _ _ _ _ _ _ run /\
      sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin eid writes; induction writes as [|[field stored] tail IH];
    intros state allocation before frame Hget Hfields Hpre.
  - exists allocation, state, before; split; [split; reflexivity|].
    split; [exact Hget|]. split; [split; [constructor|split; reflexivity]|].
    exists (KernelCSequenceRefl _ state before _ Hpre); split; constructor.
  - inversion Hfields as [|head rest [Hfield Hrange] Htail]; subst.
    destruct (sem_pend_event_private_fields_sequence environment critical sg observer origin state eid allocation
      field stored before frame Hget Hfield Hrange Hpre)
      as [middle_allocation [middle [Hlookup [Hwrite [first [Hfirst_source Hfirst_receipt]]]]]].
    pose proof (proj2 (kernel_c_sequence_resources _
      (kernel_program_selected_c_step_resources environment critical sg observer origin) _ _ _ _ _ _ _ first)) as Hmiddle.
    destruct (IH (replace_EventS
      (event_private_write state.(EventState) eid allocation field (Some stored)) state)
      middle_allocation middle frame Hlookup Htail Hmiddle)
      as [final [current [after [Hstores [Hfinal [Hrun [last [Hlast_source Hlast_receipt]]]]]]]].
    exists final, current, after; split.
    + cbn [event_create_private_stores]; exists allocation; split; assumption.
    + split; [exact Hfinal|]. split.
      * cbn [flat_map fst snd]; eapply heap_execution_append; eassumption.
      * assert (Hid : event_private_storage_rep sg eid middle_allocation **
          kernel_program_fields_inv sg (replace_EventS
            (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame |--
          event_private_storage_rep sg eid middle_allocation ** kernel_program_fields_inv sg
            (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame)
          by entailer!.
        exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ first Hid last).
        split; eapply KernelCSourceThen with (first_stopped := false) (last_stopped := false); assumption.
Qed.

Lemma sem_pend_event_publish_fields_sequence :
  forall environment critical sg observer origin state eid allocation node h (frame : Assertion),
  UCOS2_state_inv sg state -> state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  (forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg state.(TskState) node field) ->
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = nil ->
  event_fields_consistency node -> event_payload_consistency sg node ->
  event_name_valid sg state.(NameState) node -> allocation.(eventPrivateMutexPCP) = None ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) h ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state h (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)
    false (replace_EventS (event_publish state.(EventState) eid node) state) h
    (kernel_program_fields_inv sg (replace_EventS (event_publish state.(EventState) eid node) state) ** frame),
    kernel_program_selected_c_sequence_source environment critical sg observer origin None _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin state eid allocation node h frame Hvalid Hget Hqueue Himage
    Hgeneration Hkind Hfields Hwait Hconsistent Hpayload Hname Hpcp Hpre.
  assert (Hmerge : event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame |--
    kernel_program_fields_inv sg (replace_EventS (event_publish state.(EventState) eid node) state) ** frame).
  { sep_apply_l_atomic (sem_pend_event_publish_fields_merge sg state eid allocation node
      Hvalid Hget Hqueue Himage Hgeneration Hkind Hfields Hwait Hconsistent Hpayload Hname Hpcp); entailer!. }
  set (segment := @EventCreationComponent.KernelEventCreationCPublishFieldsSegment sg state eid allocation node h
    frame Hget Hname Hkind Hpre (Hmerge h Hpre)).
  assert (Hsource : kernel_event_creation_c_segment_source sg None _ _ _ _ _ _ segment).
  { unfold segment; constructor; intros; discriminate. }
  exact (sem_pend_event_creation_selected_sequence environment critical sg observer origin None
    _ _ _ _ _ _ segment Hsource).
Qed.

(** Reuse the real Prepare producer at the point where Howned/Hafter
    describe the same Reserve/StackInit/TCB/link execution. The original
    initial-local policy supplies emp; arbitrary saved locals are framed. *)
Lemma sem_pend_task_prepare_fields_sequence :
  forall environment critical sg observer origin event_observer saved_local input slot rest (frame : Assertion) before,
  input.(stack_input_call).(os_sched_call_invocation) <> observer ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input environment.(task_stack_call_continuations) saved_local sg
    input input.(stack_input_state) ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image /\
    task_create_stack_preparation_fragment sg input slot rest before after /\
    exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      input.(stack_input_state) before
      (sem_pend_task_prepare_fields_input environment.(task_stack_call_continuations) saved_local sg
        input input.(stack_input_state) ** frame) false
      (task_create_stack_input_detached input slot rest image) after
      (kernel_client_continuation_fields_publication environment.(task_stack_call_continuations)
        (task_create_continuation_local saved_local) sg (task_create_stack_prepared_publication input slot image)
        (task_create_stack_input_detached input slot rest image) ** frame),
      kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
        _ _ _ _ _ _ _ run /\
      sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin event_observer saved_local input slot rest frame before
    Hforeign Hnest Hfree Hhead Hbefore.
  set (abi := environment.(task_stack_call_continuations)).
  set (local := task_create_continuation_local saved_local).
  assert (Hsplit : sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame |--
    coq_prop (task_create_stack_input_facts sg input /\ task_stack_live_coverage input.(stack_input_state).(TskState) None) &&
    (UCOS2_fields_inv sg input.(stack_input_state) **
      task_stack_storage input.(stack_input_region)
        (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) **
      (store_parked_continuations (kernel_saved_continuation_entry abi input.(stack_input_state).(TskState) local)
        input.(stack_input_state).(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
  { unfold sem_pend_task_prepare_fields_input, kernel_client_continuation_fields_world, kernel_continuation_inv.
    rewrite kernel_program_fields_inv_split_unmap; unfold local; entailer!. }
  destruct (Hsplit before Hbefore) as [[Hfacts Hcoverage] Howned].
  destruct (sem_pend_task_fields_preparation_execution sg input slot rest _ before Hfacts Hnest Hfree Hhead Howned)
    as [image [after [Hdetach [Hsource Hafter]]]].
  destruct (task_create_stack_prepared_publication_input sg input slot rest image Hfacts Hfree Hdetach)
    as [Hvalid Hinput].
  assert (Hpointer : 0 <= task_slot_addr sg slot < 4294967296).
  { destruct Hsource as [reserved [initialized [_ [_ [detached [ready [hooked [Hpop _]]]]]]]].
    exact (proj1 (proj1 Hpop)). }
  assert (Hpriority : 0 <= (task_create_stack_input_args input).(initPrio) < 64).
  { exact (proj1 (proj2 (proj2 (proj2 (proj2 Hfacts))))). }
  assert (Hmerge : task_tcb_init_publication_fields_tail_storage sg (task_create_stack_input_args input)
      (task_create_stack_input_detached input slot rest image) slot image **
      task_stack_storage input.(stack_input_region)
        (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) **
      (store_parked_continuations (kernel_saved_continuation_entry abi input.(stack_input_state).(TskState) local)
        input.(stack_input_state).(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame) |--
    kernel_client_continuation_fields_publication abi local sg (task_create_stack_prepared_publication input slot image)
      (task_create_stack_input_detached input slot rest image) ** frame).
  { sep_apply_l_atomic (kernel_saved_continuation_map_used_map_eq environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
      input.(stack_input_state).(TskState) (task_create_stack_input_detached input slot rest image).(TskState)
      local input.(stack_input_state).(TskState).(parkedTaskStacks) eq_refl).
    assert (Hinitial : local (task_create_stack_publication_continuation
      (task_create_stack_prepared_publication input slot image)) = emp) by reflexivity.
    unfold kernel_client_continuation_fields_publication; rewrite Hinitial.
    cbn [task_create_stack_prepared_publication]; entailer!. }
  set (segment := @CreationComponent.KernelTaskCreationCPrepareFieldsSegment sg input slot rest image before after
    _ Hfacts Hnest Hfree Hdetach Hsource Howned Hafter).
  assert (Hsegment_source : kernel_task_creation_c_segment_source sg observer _ _ _ _ _ _ segment).
  { unfold segment; constructor; exact Hforeign. }
  destruct (sem_pend_task_creation_selected_sequence environment critical sg observer origin event_observer
    _ _ _ _ _ _ segment Hsegment_source) as [inner [Hinner_source Hinner_receipt]].
  assert (Hopen : sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame |--
    UCOS2_fields_inv sg input.(stack_input_state) **
      task_stack_storage input.(stack_input_region)
        (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) **
      (store_parked_continuations (kernel_saved_continuation_entry abi input.(stack_input_state).(TskState) local)
        input.(stack_input_state).(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame)).
  { intros heap Hpre; exact (proj2 (Hsplit heap Hpre)). }
  exists image, after; split; [exact Hdetach|]. split; [exact Hsource|].
  exists (KernelCSequenceAdapt _ _ _ _ _ _ _ _ _ _ Hbefore Hopen inner Hmerge).
  split; apply KernelCSourceAdapt; assumption.
Qed.

Lemma sem_pend_fields_creation_sequence_prefix :
  forall environment critical sg observer origin event_observer state before input current after output
    (run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before input false current after output),
  kernel_program_selected_c_sequence_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run ->
  sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer state current after,
    sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\ output after.
Proof.
  intros environment critical sg observer origin event_observer state before input current after output run Hsource Hreceipt.
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixCSequence environment critical sg observer
    origin event_observer _ _ _ _ _ _ _ run Hsource).
  split; [constructor; exact Hreceipt|].
  exact (proj2 (kernel_c_sequence_resources _
    (kernel_program_selected_c_step_resources environment critical sg observer origin) _ _ _ _ _ _ _ run)).
Qed.

Lemma sem_pend_event_allocate_fields_prefix :
  forall environment critical sg observer (origin : TaskInvocationOrigin) state before (frame : Assertion),
  sem_create_source_binding sg -> (kernel_program_fields_inv sg state ** frame) before ->
  exists result allocated after,
    event_create_allocate_critical state result allocated /\
    exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer state allocated after,
      sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\
      (kernel_program_fields_inv sg allocated **
       (match result with None => emp | Some (eid, image) =>
          event_private_storage_rep sg eid (sem_create_allocation_identity state image) end) ** frame) after.
Proof.
  intros environment critical sg observer origin state before frame Hbinding Hpre.
  destruct (sem_pend_event_allocate_fields_sequence environment critical sg observer origin state before frame Hbinding Hpre)
    as [result [allocated [after [Hcode [run [Hsource Hreceipt]]]]]].
  exists result, allocated, after; split; [exact Hcode|].
  eapply sem_pend_fields_creation_sequence_prefix; eassumption.
Qed.

Lemma sem_pend_task_prepare_fields_prefix :
  forall environment critical sg observer (origin : TaskInvocationOrigin) (event_observer : option nat)
    saved_local input slot rest (frame : Assertion) before,
  input.(stack_input_call).(os_sched_call_invocation) <> observer ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input environment.(task_stack_call_continuations) saved_local sg
    input input.(stack_input_state) ** frame) before ->
  exists image after,
    task_create_stack_preparation_fragment sg input slot rest before after /\
    exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer
      input.(stack_input_state) (task_create_stack_input_detached input slot rest image) after,
      sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\
      (kernel_client_continuation_fields_publication environment.(task_stack_call_continuations)
        (task_create_continuation_local saved_local) sg (task_create_stack_prepared_publication input slot image)
        (task_create_stack_input_detached input slot rest image) ** frame) after.
Proof.
  intros environment critical sg observer origin event_observer saved_local input slot rest frame before
    Hforeign Hnest Hfree Hhead Hpre.
  destruct (sem_pend_task_prepare_fields_sequence environment critical sg observer origin event_observer
    saved_local input slot rest frame before Hforeign Hnest Hfree Hhead Hpre)
    as [image [after [Hdetach [Hcode [run [Hsource Hreceipt]]]]]].
  exists image, after; split; [exact Hcode|].
  eapply sem_pend_fields_creation_sequence_prefix; eassumption.
Qed.

Lemma sem_pend_creator_publish_fields_sequence :
  forall environment critical sg observer origin creator state eid allocation image h (frame : Assertion),
  UCOS2_state_inv sg state -> state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  mutex_del_creator_arguments creator ->
  allocation.(eventPrivateStorage) = event_create_stores_image image (mutex_del_creator_fields sg creator) ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) h ->
  exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state h (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)
    false (mutex_del_creator_published_state creator state eid allocation) h
    (kernel_program_fields_inv sg (mutex_del_creator_published_state creator state eid allocation) ** frame),
    kernel_program_selected_c_sequence_source environment critical sg observer origin None _ _ _ _ _ _ _ run /\
    sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin creator state eid allocation image h frame
    Hvalid Hget Hqueue Hpcp Hargs Himage Hpre.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hname : event_name_valid sg state.(NameState) (mutex_del_creator_event creator allocation)).
  { destruct creator; apply event_name_valid_disabled; exact Hnames. }
  assert (Hkind : (mutex_del_creator_event creator allocation).(eventType) <> OS_EVENT_TYPE_MUTEX).
  { destruct creator; discriminate. }
  assert (Hmerge : event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame |--
    kernel_program_fields_inv sg (mutex_del_creator_published_state creator state eid allocation) ** frame).
  { sep_apply_l_atomic (sem_pend_creator_publish_fields_resources sg creator state eid allocation image
      Hvalid Hget Hqueue Hpcp Hargs Himage); entailer!. }
  set (segment := @EventCreationComponent.KernelEventCreationCPublishFieldsSegment sg state eid allocation
    (mutex_del_creator_event creator allocation) h frame Hget Hname Hkind Hpre (Hmerge h Hpre)).
  assert (Hsource : kernel_event_creation_c_segment_source sg None _ _ _ _ _ _ segment).
  { unfold segment; constructor; intros; discriminate. }
  exact (sem_pend_event_creation_selected_sequence environment critical sg observer origin None
    _ _ _ _ _ _ segment Hsource).
Qed.

Lemma sem_pend_creator_private_fields_sequence :
  forall environment critical sg observer origin creator state eid allocation before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  mutex_del_creator_arguments creator ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) before ->
  exists final initialized after,
    event_create_private_stores eid (mutex_del_creator_fields sg creator) state tt initialized /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes (event_pool_addr sg eid) (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after /\
    exists run : kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
      state before (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)
      false (mutex_del_creator_published_state creator initialized eid final) after
      (kernel_program_fields_inv sg (mutex_del_creator_published_state creator initialized eid final) ** frame),
      kernel_program_selected_c_sequence_source environment critical sg observer origin None _ _ _ _ _ _ _ run /\
      sem_pend_selected_c_sequence_receipt environment critical sg observer origin _ _ _ _ _ _ _ run.
Proof.
  intros environment critical sg observer origin creator state eid allocation before frame Hget Hqueue Hpcp Hargs Hpre.
  assert (Hextract : event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
      (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame)).
  { unfold kernel_program_fields_inv; entailer!. }
  pose proof (proj1 (Hextract before Hpre)) as Hvalid.
  destruct (sem_pend_event_private_prefix_fields_sequence environment critical sg observer origin eid
    (mutex_del_creator_fields sg creator) state allocation before frame Hget
    (mutex_del_creator_fields_in_range sg creator Hargs) Hpre)
    as [final [initialized [after [Hstores [Hfinal [Hwrites [first [Hfirst_source Hfirst_receipt]]]]]]]].
  pose proof (proj2 (kernel_c_sequence_resources _
    (kernel_program_selected_c_step_resources environment critical sg observer origin) _ _ _ _ _ _ _ first)) as Hafter.
  pose proof (event_create_private_stores_preserves_validity sg eid _ state tt initialized Hvalid Hstores) as Hinitialized.
  destruct (event_create_private_stores_post_allocation eid _ state tt initialized allocation Hget Hstores)
    as [actual [Hactual [_ [_ [Hqueue_final Himage]]]]].
  assert (actual = final) by congruence; subst actual.
  pose proof (event_create_private_stores_mutex_pcp_eq eid _ state tt initialized allocation final Hget Hstores Hfinal)
    as Hpcp_final.
  destruct (sem_pend_creator_publish_fields_sequence environment critical sg observer origin creator initialized eid final
    allocation.(eventPrivateStorage) after frame Hinitialized Hfinal ltac:(congruence) ltac:(congruence)
    Hargs Himage Hafter) as [last [Hlast_source Hlast_receipt]].
  assert (Hid : event_private_storage_rep sg eid final ** kernel_program_fields_inv sg initialized ** frame |--
    event_private_storage_rep sg eid final ** kernel_program_fields_inv sg initialized ** frame) by entailer!.
  exists final, initialized, after; split; [exact Hstores|]. split; [exact Hwrites|].
  exists (KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _ first Hid last).
  split; eapply KernelCSourceThen with (first_stopped := false) (last_stopped := false); assumption.
Qed.

(** Immediate consumption at the original pending creator owner. The
    existential ECB is opened once, then retained through its actual stores,
    publication, source and receipt; the parked map stays the same frame. *)
Lemma sem_pend_creator_pending_fields_prefix :
  forall environment critical local sg observer (origin : TaskInvocationOrigin)
    creator pointer state before (frame : Assertion),
  mutex_del_creator_arguments creator ->
  (sem_pend_creator_fields_pending environment.(task_stack_call_continuations) local sg pointer state ** frame) before ->
  exists eid final initialized after,
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after /\
    exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer state
      (mutex_del_creator_published_state creator initialized eid final) after,
      sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\
      (kernel_client_continuation_fields_world environment.(task_stack_call_continuations) local sg
        (mutex_del_creator_published_state creator initialized eid final) ** frame) after.
Proof.
  intros environment critical local sg observer origin creator pointer state before frame Hargs Hpre.
  set (abi := environment.(task_stack_call_continuations)).
  assert (Hopen : sem_pend_creator_fields_pending abi local sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) None) &&
      (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state **
       (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold sem_pend_creator_fields_pending; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_continuation_fields_world, kernel_continuation_inv, kernel_program_fields_inv; entailer!. }
  destruct (Hopen before Hpre)
    as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp [Hvalid Hcoverage]]]]] Howned]]].
  destruct (sem_pend_creator_private_fields_sequence environment critical sg observer origin creator state eid allocation
    before _ Hget Hqueue Hpcp Hargs Howned)
    as [final [initialized [after [Hstores [Hwrites [run [Hsource Hreceipt]]]]]]].
  assert (Htasks : initialized.(TskState) = state.(TskState)).
  { pose proof (event_create_private_stores_published_frame eid _ state tt initialized Hstores); tauto. }
  assert (Hclose : kernel_program_fields_inv sg (mutex_del_creator_published_state creator initialized eid final) **
    (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_continuation_fields_world abi local sg
      (mutex_del_creator_published_state creator initialized eid final) ** frame).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
      mutex_del_creator_published_state; cbn [replace_EventS TskState].
    rewrite Htasks; entailer!. }
  destruct (sem_pend_fields_creation_sequence_prefix environment critical sg observer origin None _ _ _ _ _ _
    run Hsource Hreceipt) as [prefix [Hprefix Hpost]].
  exists eid, final, initialized, after; split; [rewrite Hpointer; exact Hwrites|].
  exists prefix; split; [exact Hprefix|exact (Hclose after Hpost)].
Qed.

(** The original Extra step fixes image and final heap. Determinism relates
    the physical producer to that same supplied step, before returning its
    original effect and its actual next owner together with the C prefix. *)
Lemma sem_pend_task_prepare_fields_extra_prefix :
  forall environment critical saved_local sg observer (origin : TaskInvocationOrigin)
    (event_observer : option nat) cut before next after state (frame : Assertion),
  task_create_stack_heap_step sg cut before next after ->
  sem_pend_task_prepare_observer_cut observer cut ->
  (sem_pend_task_prepare_fields_resources environment.(task_stack_call_continuations) saved_local sg cut state ** frame) before ->
  exists returned,
    task_create_stack_heap_effect sg cut state next returned /\
    exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment critical sg observer state returned after,
      sem_pend_sched_prefix_receipt environment critical sg observer _ _ _ prefix /\
      (sem_pend_task_prepare_fields_resources environment.(task_stack_call_continuations) saved_local sg next returned ** frame) after.
Proof.
  intros environment critical saved_local sg observer origin event_observer cut before next after state frame Hstep Hforeign Hpre.
  destruct Hstep as [input slot rest image before after Hnest Hfree Hhead Himage Hrun].
  assert (Hstate : state = input.(stack_input_state)).
  { assert (Hopen : sem_pend_task_prepare_fields_resources environment.(task_stack_call_continuations)
      saved_local sg (KernelClientHeapExtra input) state ** frame |--
      coq_prop (state = input.(stack_input_state)) && TT).
    { cbn [sem_pend_task_prepare_fields_resources]; unfold sem_pend_task_prepare_fields_input; entailer!. }
    exact (proj1 (Hopen before Hpre)). }
  subst state.
  destruct (sem_pend_task_prepare_fields_sequence environment critical sg observer origin event_observer saved_local
    input slot rest frame before Hforeign Hnest Hfree Hhead Hpre)
    as [actual [produced [Hdetach [Hprepare [run [Hsource Hreceipt]]]]]].
  assert (Hactual : input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some actual)
    by exact (proj2 (proj2 (proj2 Hdetach))).
  assert (actual = image) by congruence; subst actual.
  assert (produced = after) by (eapply task_create_stack_preparation_final_eq; eassumption); subst produced.
  exists (task_create_stack_input_detached input slot rest image); split; [constructor|].
  eapply sem_pend_fields_creation_sequence_prefix; eassumption.
Qed.
