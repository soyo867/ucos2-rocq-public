Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.sched Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.event Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_allocation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_dispatch_receipt_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Existing physical owners other than the Event and Queue modules. The
    six Flag fields remain present; this does not add their padding. *)
Definition sem_pend_fields_event_queue_frame sg state : Assertion :=
  flag_fields_configured_rep sg state.(FlagState) **
  UCOS2_selected_rep sg state (fun m =>
    match m with FlagModule | EventModule | QueueModule => false | _ => true end) **
  unmap_table_rep sg.

Lemma sem_pend_fields_split_event_queue : forall sg state,
  kernel_program_fields_inv sg state --||--
    coq_prop (UCOS2_state_inv sg state) &&
    (event_raw_rep sg state.(TskState) state.(EventState) **
     queue_storage_rep sg state.(EventState) ** sem_pend_fields_event_queue_frame sg state).
Proof.
  intros sg state; unfold kernel_program_fields_inv, kernel_program_fields_rep,
    UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag, UCOS2_raw_rep_missing_module,
    sem_pend_fields_event_queue_frame, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  split; entailer!.
Qed.

Lemma sem_pend_fields_private_write_frame : forall sg state eid allocation field value,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_program_fields_inv sg state |--
    kernel_program_fields_inv sg
      (replace_EventS (event_private_write state.(EventState) eid allocation field value) state).
Proof.
  intros sg state eid allocation field value Hget.
  rewrite !sem_pend_fields_split_event_queue; Intros.
  match goal with H : UCOS2_state_inv sg state |- _ =>
    pose proof (UCOS2_event_private_write_preserves_validity sg state eid allocation field value H Hget)
      as Hpost end.
  cbn [replace_EventS TskState EventState].
  rewrite (queue_storage_event_private_write_eq sg state.(EventState) eid allocation field value Hget).
  unfold sem_pend_fields_event_queue_frame, UCOS2_selected_rep;
    cbn [replace_EventS UCOS2_module_rep].
  unfold event_raw_rep, event_free_storage_rep, event_free_root_rep;
    cbn [event_private_write event_set_lifecycle]; entailer!.
Qed.

Lemma sem_pend_private_field_fields_resources : forall sg state eid allocation field stored before
  (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_create_field_value_in_range field stored ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) before ->
  exists final after,
    (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
      eid = Some final /\
    kernel_heap_execution (event_create_field_writes (event_pool_addr sg eid) field stored) before after /\
    (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg
      (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame) after.
Proof.
  intros sg state eid allocation field stored before frame Hget Hfield Hrange Hpre.
  set (final := {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
    eventPrivateGeneration := allocation.(eventPrivateGeneration);
    eventPrivateQueue := allocation.(eventPrivateQueue);
    eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
    eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |}).
  assert (Hlookup :
    (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
      eid = Some final) by apply kernel_map_set_same.
  assert (Hsplit : event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame |--
    event_cell (event_pool_addr sg eid) field (allocation.(eventPrivateStorage) field) **
    (event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) field ** kernel_program_fields_inv sg state ** frame)).
  { unfold event_private_storage_rep.
    sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) allocation.(eventPrivateStorage) field Hfield); entailer!. }
  destruct (event_create_field_store_execution (event_pool_addr sg eid) field
    (allocation.(eventPrivateStorage) field) stored _ before Hrange (Hsplit before Hpre))
    as [after [Hrun Hafter]].
  assert (Hmerge : event_cell (event_pool_addr sg eid) field (Some stored) **
    (event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) field ** kernel_program_fields_inv sg state ** frame) |--
    event_private_storage_rep sg eid final ** kernel_program_fields_inv sg
      (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame).
  { unfold event_private_storage_rep, final; cbn [eventPrivateStorage].
    sep_apply_l_atomic (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) allocation.(eventPrivateStorage) field (Some stored) Hfield).
    sep_apply_l_atomic (sem_pend_fields_private_write_frame sg state eid allocation field (Some stored) Hget).
    entailer!. }
  exists final, after; split; [exact Hlookup|]. split; [exact Hrun|exact (Hmerge after Hafter)].
Qed.

Lemma sem_pend_private_prefix_fields_resources : forall sg eid writes state allocation before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  Forall (fun write => In (fst write) (event_fields sg.(osKernelConfig).(cfgEventNames)) /\
    event_create_field_value_in_range (fst write) (snd write)) writes ->
  (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state ** frame) before ->
  exists final next after,
    event_create_private_stores eid writes state tt next /\
    next.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes (event_pool_addr sg eid) (fst write) (snd write)) writes)
      before after /\
    (event_private_storage_rep sg eid final ** kernel_program_fields_inv sg next ** frame) after.
Proof.
  intros sg eid writes; induction writes as [|[field stored] rest IH];
    intros state allocation before frame Hget Hfields Hpre.
  - exists allocation, state, before; split; [split; reflexivity|].
    split; [exact Hget|]. split; [split; [constructor|split; reflexivity]|exact Hpre].
  - inversion Hfields as [|head tail [Hfield Hrange] Hrest]; subst.
    destruct (sem_pend_private_field_fields_resources sg state eid allocation field stored before frame
      Hget Hfield Hrange Hpre) as [middle_allocation [middle [Hlookup [Hwrite Hmiddle]]]].
    destruct (IH (replace_EventS
        (event_private_write state.(EventState) eid allocation field (Some stored)) state)
        middle_allocation middle frame Hlookup Hrest Hmiddle)
      as [final [next [after [Htail [Hfinal [Hrun Hafter]]]]]].
    exists final, next, after; split.
    + cbn [event_create_private_stores]; exists allocation; split; assumption.
    + split; [exact Hfinal|]. split; [cbn [flat_map fst snd]; eapply heap_execution_append; eassumption|exact Hafter].
Qed.

Lemma sem_pend_event_publish_fields_merge : forall sg state eid allocation node,
  UCOS2_state_inv sg state -> state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  (forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg state.(TskState) node field) ->
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = nil ->
  event_fields_consistency node -> event_payload_consistency sg node ->
  event_name_valid sg state.(NameState) node -> allocation.(eventPrivateMutexPCP) = None ->
  event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state |--
  kernel_program_fields_inv sg (replace_EventS (event_publish state.(EventState) eid node) state).
Proof.
  intros sg state eid allocation node Hvalid Hget Hprivate Himage Hgeneration Hnonmutex Hqueue Hempty
    Hfields Hpayload Hname Hpcp.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_private_not_free sg state.(EventState) eid allocation Hpool Hget) as [_ [_ Hnone]].
  pose proof (UCOS2_event_publish_preserves_validity sg state eid allocation node
    Hvalid Hget Hgeneration Hnonmutex Hqueue Hempty Hfields Hpayload Hname Hpcp) as Hpost.
  rewrite !sem_pend_fields_split_event_queue; Intros.
  sep_apply_l_atomic (event_publish_reconstructs_raw_rep_on_fields
    sg state.(TskState) state.(EventState) eid allocation node Hpool Hget Himage).
  sep_apply_l_atomic (queue_event_publish_preserves_storage
    sg state.(EventState) eid allocation node Hnone Hget Hprivate Hqueue).
  unfold sem_pend_fields_event_queue_frame, UCOS2_selected_rep;
    cbn [replace_EventS UCOS2_module_rep TskState EventState FlagState SchedState IntrState
      TickState MemoryState TimerState StatsState ControlState NameState]; entailer!.
Qed.

Lemma sem_pend_creator_publish_fields_resources : forall sg creator state eid allocation image,
  UCOS2_state_inv sg state -> state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  mutex_del_creator_arguments creator ->
  allocation.(eventPrivateStorage) = event_create_stores_image image (mutex_del_creator_fields sg creator) ->
  event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state |--
  kernel_program_fields_inv sg (mutex_del_creator_published_state creator state eid allocation).
Proof.
  intros sg creator state eid allocation image Hvalid Hget Hqueue Hpcp Hargs Himage.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  destruct creator; cbn [mutex_del_creator_fields mutex_del_creator_arguments] in Hargs, Himage;
    rewrite event_create_stores_image_initialization_eq in Himage;
    unfold mutex_del_creator_published_state; cbn [mutex_del_creator_event].
  - eapply sem_pend_event_publish_fields_merge;
      [exact Hvalid|exact Hget|exact Hqueue| |reflexivity|discriminate|reflexivity|reflexivity| | | |exact Hpcp].
    + eapply sem_create_image_matches_event; exact Himage.
    + apply sem_create_event_fields_consistency.
    + apply sem_create_event_payload_consistency; lia.
    + apply event_name_valid_disabled; exact Hnames.
  - eapply sem_pend_event_publish_fields_merge;
      [exact Hvalid|exact Hget|exact Hqueue| |reflexivity|discriminate|reflexivity|reflexivity| | | |exact Hpcp].
    + eapply mbox_create_image_matches_event; exact Himage.
    + apply mbox_create_event_fields_consistency.
    + apply mbox_create_event_payload_consistency; exact Hargs.
    + apply event_name_valid_disabled; exact Hnames.
Qed.

(** Every literal store has its own lookup and input facts, derived along
    this finite store list. No invariant over an unrelated future trace is
    requested, and the last state may still contain a private object. *)
Lemma sem_pend_creator_stores_client_receipt : forall external port actor creator sg observer origin eid writes
  state result returned,
  actor <> Some observer -> UCOS2_state_inv sg state ->
  event_create_private_stores eid writes state result returned ->
  exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
    sg observer None origin state false origin returned,
  sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
    sg observer None origin state false origin returned trace.
Proof.
  intros external port actor creator sg observer origin eid writes; induction writes as [|[field stored] rest IH];
    intros state result returned Hforeign Hvalid Hstores.
  - destruct Hstores as [_ ->].
    exists (@KernelClientTaskSourceNil external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state); constructor.
  - destruct Hstores as [allocation [Hget Htail]].
    set (middle := replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state).
    assert (Hmiddle : UCOS2_state_inv sg middle).
    { apply UCOS2_event_private_write_preserves_validity; assumption. }
    destruct (IH middle result returned Hforeign Hmiddle Htail) as [tail Htail_receipt].
    assert (Hhead : exists trace : kernel_client_task_source_trace external port
      (mutex_del_creator_source_client actor creator) sg observer None origin state false origin middle,
      sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state false origin middle trace).
    { eapply sem_pend_dispatch_framed_step_receipt with
        (action := event_create_private_store_client actor eid allocation field stored).
      - apply MutexDelCreatorSourceStore.
      - exact Hforeign.
      - intros; discriminate.
      - split; [exact Hget|reflexivity].
      - reflexivity.
      - apply TmrTaskCallNontimer; [constructor|split; [exact Hget|reflexivity]].
      - apply sem_pend_source_state_facts_from_valid; exact Hvalid. }
    destruct Hhead as [head Hhead_receipt].
    exact (sem_pend_dispatch_client_receipt_append external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state false origin middle head Hhead_receipt false origin returned tail Htail_receipt).
Qed.

Definition sem_pend_creator_fields_pending {external platform port}
  (abi : Armv7aContinuationABI external platform port) local sg pointer state : Assertion :=
  EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
    (kernel_client_continuation_fields_world abi local sg state ** event_private_storage_rep sg eid allocation).

Definition sem_pend_creator_fields_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) local sg
  (cut : KernelClientHeapCut Z) state : Assertion :=
  match cut with
  | KernelClientHeapClosed => kernel_client_continuation_fields_world abi local sg state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_continuation_fields_publication abi local sg publication state
  | KernelClientHeapExtra pointer => sem_pend_creator_fields_pending abi local sg pointer state
  end.

Lemma sem_pend_creator_fields_resources_valid :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local sg cut state heap (frame : Assertion),
  (sem_pend_creator_fields_resources abi local sg cut state ** frame) heap -> UCOS2_state_inv sg state.
Proof.
  intros external platform port abi local sg cut state heap frame Hpre.
  assert (Hopen : sem_pend_creator_fields_resources abi local sg cut state ** frame |--
    coq_prop (UCOS2_state_inv sg state) && TT).
  { destruct cut; cbn [sem_pend_creator_fields_resources].
    - unfold kernel_client_continuation_fields_world, kernel_continuation_inv, kernel_program_fields_inv; entailer!.
    - unfold kernel_client_continuation_fields_publication; entailer!.
    - unfold sem_pend_creator_fields_pending; Intros eid allocation.
      unfold kernel_client_continuation_fields_world, kernel_continuation_inv, kernel_program_fields_inv; entailer!. }
  exact (proj1 (Hopen heap Hpre)).
Qed.

Lemma sem_pend_creator_allocate_fields_pending : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg state before cut after (frame : Assertion),
  mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after ->
  (kernel_client_continuation_fields_world abi local sg state ** frame) before ->
  exists returned,
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned /\
    (sem_pend_creator_fields_resources abi local sg cut returned ** frame) after.
Proof.
  intros external platform port abi local sg state before cut after frame Hsource Hpre.
  destruct (sem_pend_allocation_fields_extra_resources external platform port abi local sg
    KernelClientHeapClosed before cut after state frame Hsource Hpre) as [returned [Hstep Hafter]].
  exists returned; split; [exact Hstep|]. destruct Hstep.
  - exact Hafter.
  - pose proof (proj2 (event_create_allocate_critical_private_result state eid image returned H)) as Hget.
    assert (Hclose : sem_pend_allocation_fields_resources abi local sg
        (KernelClientHeapExtra (event_pool_addr sg eid)) returned ** frame |--
      sem_pend_creator_fields_resources abi local sg (KernelClientHeapExtra (event_pool_addr sg eid)) returned ** frame).
    { cbn [sem_pend_allocation_fields_resources]; Intros found allocation.
      assert (Hbindings : event_pool_addr sg eid = event_pool_addr sg found /\
        returned.(EventState).(eventLifecycle).(eventPrivate) found = Some allocation) by tauto.
      destruct Hbindings as [Haddress Hlookup].
      assert (found = eid) by (apply event_pool_addr_injective with (sg := sg); congruence); subst found.
      assert (allocation = sem_create_allocation_identity state image)
        by (unfold sem_create_allocation_identity; congruence); subst allocation.
      cbn [sem_pend_creator_fields_resources]; unfold sem_pend_creator_fields_pending.
      Exists eid (sem_create_allocation_identity state image).
      cbn [sem_create_allocation_identity eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
    exact (Hclose after Hafter).
Qed.

Lemma sem_pend_creator_initialization_fields_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg creator pointer state before (frame : Assertion),
  mutex_del_creator_arguments creator ->
  (sem_pend_creator_fields_pending abi local sg pointer state ** frame) before ->
  exists eid allocation initialized final after,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    event_create_private_stores eid (mutex_del_creator_fields sg creator) state tt initialized /\
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after /\
    (kernel_client_continuation_fields_world abi local sg
       (mutex_del_creator_published_state creator initialized eid final) ** frame) after.
Proof.
  intros external platform port abi local sg creator pointer state before frame Hargs Hpre.
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
  destruct (sem_pend_private_prefix_fields_resources sg eid (mutex_del_creator_fields sg creator) state allocation
    before _ Hget (mutex_del_creator_fields_in_range sg creator Hargs) Howned)
    as [final [initialized [after [Hstores [Hfinal [Hwrites Hafter]]]]]].
  pose proof (event_create_private_stores_preserves_validity sg eid _ state tt initialized Hvalid Hstores) as Hinitialized.
  destruct (event_create_private_stores_post_allocation eid _ state tt initialized allocation Hget Hstores)
    as [actual [Hactual [_ [_ [Hqueue_final Himage]]]]].
  assert (actual = final) by congruence; subst actual.
  pose proof (event_create_private_stores_mutex_pcp_eq eid _ state tt initialized allocation final
    Hget Hstores Hfinal) as Hpcp_final.
  assert (Htasks : initialized.(TskState) = state.(TskState)).
  { pose proof (event_create_private_stores_published_frame eid _ state tt initialized Hstores); tauto. }
  assert (Hclose : event_private_storage_rep sg eid final ** kernel_program_fields_inv sg initialized **
    (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_continuation_fields_world abi local sg
      (mutex_del_creator_published_state creator initialized eid final) ** frame).
  { sep_apply_l_atomic (sem_pend_creator_publish_fields_resources sg creator initialized eid final
      allocation.(eventPrivateStorage) Hinitialized Hfinal ltac:(congruence) ltac:(congruence) Hargs Himage).
    unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
      mutex_del_creator_published_state; cbn [replace_EventS TskState].
    rewrite Htasks; entailer!. }
  exists eid, allocation, initialized, final, after.
  split; [exact Hpointer|]. split; [exact Hget|]. split; [exact Hstores|]. split; [exact Hfinal|].
  split; [rewrite Hpointer; exact Hwrites|exact (Hclose after Hafter)].
Qed.

Lemma sem_pend_creator_publication_fields_extra : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local creator,
  mutex_del_creator_arguments creator ->
  forall sg cut before next after state (frame : Assertion),
  mutex_del_creator_publication_step creator sg cut before next after ->
  (sem_pend_creator_fields_resources abi local sg cut state ** frame) before ->
  exists returned,
    mutex_del_creator_publication_effect creator sg cut state next returned /\
    (sem_pend_creator_fields_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port abi local creator Hargs sg cut before next after state frame Hsource Hpre.
  destruct Hsource as [before cut after Hallocate|pointer before after Hwrites].
  - destruct (sem_pend_creator_allocate_fields_pending external platform port abi local sg state before cut after
      frame Hallocate Hpre) as [returned [Hstep Hafter]].
    exists returned; split; [constructor; exact Hstep|exact Hafter].
  - destruct (sem_pend_creator_initialization_fields_publish external platform port abi local sg creator pointer state
      before frame Hargs Hpre) as [eid [allocation [initialized [final [produced
        [Hpointer [Hget [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    exists (mutex_del_creator_published_state creator initialized eid final).
    split; [econstructor; eassumption|exact Hafter].
Qed.

Lemma sem_pend_dispatch_client_receipt_inclusion :
  forall external port clients other_clients sg observer event_observer,
  (forall action, clients action -> other_clients action) ->
  forall first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer first before stopped last after),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer first before stopped last after trace ->
  exists included : kernel_client_task_source_trace external port other_clients sg observer event_observer
      first before stopped last after,
    sem_pend_client_source_local_receipt external port other_clients sg observer event_observer
      first before stopped last after included.
Proof.
  intros external port clients other_clients sg observer event_observer Hinclusion first before stopped last after trace Hreceipt.
  induction Hreceipt as [origin state|action first before middle transient last after stopped
    member foreign event_foreign step execution tail receipt facts Htail IH].
  - exists (@KernelClientTaskSourceNil external port other_clients sg observer event_observer origin state); constructor.
  - destruct IH as [included Hinclude].
    exists (@KernelClientTaskSourceStep external port other_clients sg observer event_observer
      action first before middle transient last after stopped (Hinclusion action member)
      foreign event_foreign step execution included); constructor; assumption.
Qed.

Lemma sem_pend_creator_publication_effect_receipt : forall external port actor creator sg observer origin cut state next returned,
  actor <> Some observer -> UCOS2_state_inv sg state ->
  mutex_del_creator_publication_effect creator sg cut state next returned ->
  exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state false origin returned trace.
Proof.
  intros external port actor creator sg observer origin cut state next returned Hforeign Hvalid Heffect.
  destruct Heffect as [cut state returned Hallocate|pointer state eid allocation initialized final
    Hpointer Hget Hstores Hfinal].
  - assert (Hfacts : sem_pend_source_state_facts sg state) by (apply sem_pend_source_state_facts_from_valid; exact Hvalid).
    destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer KernelClientHeapClosed
      state cut returned origin Hforeign I (KernelClientHeapExtraState _ _ _ _ _ _ Hallocate) Hfacts)
      as [_ [trace Hreceipt]].
    eapply sem_pend_dispatch_client_receipt_inclusion; [intros action Hmember; constructor; exact Hmember|exact Hreceipt].
  - destruct (sem_pend_creator_stores_client_receipt external port actor creator sg observer origin eid
      (mutex_del_creator_fields sg creator) state tt initialized Hforeign Hvalid Hstores) as [prefix Hprefix].
    pose proof (event_create_private_stores_preserves_validity sg eid _ state tt initialized Hvalid Hstores) as Hinitialized.
    assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
    { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
    assert (Hpublish : exists suffix : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
      sg observer None origin initialized false origin (mutex_del_creator_published_state creator initialized eid final),
      sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
        sg observer None origin initialized false origin (mutex_del_creator_published_state creator initialized eid final) suffix).
    { eapply sem_pend_dispatch_framed_step_receipt with
        (action := event_create_publication_client actor eid final (mutex_del_creator_event creator final)).
      - apply MutexDelCreatorSourcePublish.
      - exact Hforeign.
      - intros; discriminate.
      - split; [exact Hfinal|]. split; [apply event_name_valid_disabled; exact Hnames|reflexivity].
      - reflexivity.
      - apply TmrTaskCallNontimer; [constructor|].
        split; [exact Hfinal|]. split; [apply event_name_valid_disabled; exact Hnames|reflexivity].
      - apply sem_pend_source_state_facts_from_valid; exact Hinitialized. }
    destruct Hpublish as [suffix Hsuffix].
    exact (sem_pend_dispatch_client_receipt_append external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state false origin initialized prefix Hprefix false origin
      (mutex_del_creator_published_state creator initialized eid final) suffix Hsuffix).
Qed.

Lemma sem_pend_creator_pending_enter_fields : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg pointer state before after (frame : Assertion),
  kernel_client_int_enter_fragment sg before after ->
  (sem_pend_creator_fields_pending abi local sg pointer state ** frame) before ->
  (sem_pend_creator_fields_pending abi local sg pointer (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi local sg pointer state before after frame Hsource Hpre.
  assert (Hopen : sem_pend_creator_fields_pending abi local sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
      (kernel_client_continuation_fields_world abi local sg state **
       (event_private_storage_rep sg eid allocation ** frame))).
  { unfold sem_pend_creator_fields_pending; Intros eid allocation; Exists eid allocation; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [Hfacts Howned]]].
  pose proof (kernel_client_int_enter_continuation_fields_resources external platform port abi local sg state
    (event_private_storage_rep sg eid allocation ** frame) before after Howned Hsource) as Hafter.
  assert (Hclose : kernel_client_continuation_fields_world abi local sg (os_int_enter_state state) **
    (event_private_storage_rep sg eid allocation ** frame) |--
    sem_pend_creator_fields_pending abi local sg pointer (os_int_enter_state state) ** frame).
  { unfold sem_pend_creator_fields_pending; Exists eid allocation.
    unfold os_int_enter_state; cbn [replace_IntrS EventState]; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma sem_pend_creator_pending_exit_fields : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg pointer state before after (frame : Assertion),
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (sem_pend_creator_fields_pending abi local sg pointer state ** frame) before ->
  (sem_pend_creator_fields_pending abi local sg pointer
     (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi local sg pointer state before after frame Hsource Hpre.
  assert (Hopen : sem_pend_creator_fields_pending abi local sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
      (kernel_client_continuation_fields_world abi local sg state **
       (event_private_storage_rep sg eid allocation ** frame))).
  { unfold sem_pend_creator_fields_pending; Intros eid allocation; Exists eid allocation; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [Hfacts Howned]]].
  pose proof (kernel_client_int_exit_continuation_fields_resources external platform port abi local sg state
    (event_private_storage_rep sg eid allocation ** frame) before after Howned Hsource) as Hafter.
  assert (Hclose : kernel_client_continuation_fields_world abi local sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
    (event_private_storage_rep sg eid allocation ** frame) |--
    sem_pend_creator_fields_pending abi local sg pointer
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { unfold sem_pend_creator_fields_pending; Exists eid allocation.
    unfold os_int_exit_counter_state; cbn [replace_IntrS EventState]; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma sem_pend_creator_pending_field_fields : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg creator pointer state field stored before after
  (frame : Assertion),
  mutex_del_creator_arguments creator -> In (field, stored) (mutex_del_creator_fields sg creator) ->
  kernel_heap_execution (event_create_field_writes pointer field stored) before after ->
  (sem_pend_creator_fields_pending abi local sg pointer state ** frame) before ->
  exists eid allocation,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (sem_pend_creator_fields_pending abi local sg pointer
      (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame) after.
Proof.
  intros external platform port abi local sg creator pointer state field stored before after frame
    Hargs Hin Hsource Hpre.
  pose proof (mutex_del_creator_fields_in_range sg creator Hargs) as Hranges.
  rewrite Forall_forall in Hranges; specialize (Hranges (field, stored) Hin).
  cbn [fst snd] in Hranges; destruct Hranges as [Hfield Hrange].
  assert (Hopen : sem_pend_creator_fields_pending abi local sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        task_stack_live_coverage state.(TskState) None) &&
      (event_private_storage_rep sg eid allocation ** kernel_program_fields_inv sg state **
       (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold sem_pend_creator_fields_pending; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp Hcoverage]]]] Howned]]].
  destruct (sem_pend_private_field_fields_resources sg state eid allocation field stored before _
    Hget Hfield Hrange Howned) as [final [produced [Hlookup [Hrun Hpost]]]].
  rewrite <- Hpointer in Hrun.
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (updated := {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
    eventPrivateGeneration := allocation.(eventPrivateGeneration); eventPrivateQueue := allocation.(eventPrivateQueue);
    eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
    eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |}).
  assert (Hupdated : (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
    eid = Some updated) by apply kernel_map_set_same.
  assert (final = updated) by congruence; subst final.
  exists eid, allocation; split; [exact Hpointer|]. split; [exact Hget|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold sem_pend_creator_fields_pending; Exists eid updated.
    unfold kernel_client_continuation_fields_world, kernel_continuation_inv.
    cbn [replace_EventS EventState TskState].
    unfold updated; cbn [eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
  exact (Hclose after Hpost).
Qed.

Lemma sem_pend_creator_interrupt_fields_extra : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local creator,
  mutex_del_creator_arguments creator ->
  forall sg cut before next after state (frame : Assertion),
  mutex_del_creator_interrupt_step creator sg cut before next after ->
  (sem_pend_creator_fields_resources abi local sg cut state ** frame) before ->
  exists returned,
    mutex_del_creator_interrupt_effect creator sg cut state next returned /\
    (sem_pend_creator_fields_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port abi local creator Hargs sg cut before next after state frame Hsource Hpre.
  destruct Hsource.
  - destruct (sem_pend_creator_publication_fields_extra external platform port abi local creator Hargs
      sg cut before next after state frame H Hpre) as [returned [Heffect Hpost]].
    exists returned; split; [constructor; exact Heffect|exact Hpost].
  - exists (os_int_enter_state state); split; [apply MutexDelCreatorInterruptEnterState|].
    eapply sem_pend_creator_pending_enter_fields; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [apply MutexDelCreatorInterruptExitState|].
    eapply sem_pend_creator_pending_exit_fields; eassumption.
  - destruct (sem_pend_creator_pending_field_fields external platform port abi local sg creator pointer state field stored
      before after frame Hargs H H0 Hpre) as [eid [allocation [Hpointer [Hget Hpost]]]].
    exists (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state).
    split; [eapply MutexDelCreatorInterruptFieldState; eassumption|exact Hpost].
Qed.

Lemma sem_pend_creator_interrupt_effect_receipt : forall external port actor creator sg observer origin cut state next returned,
  actor <> Some observer -> UCOS2_state_inv sg state ->
  mutex_del_creator_interrupt_effect creator sg cut state next returned ->
  exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state false origin returned trace.
Proof.
  intros external port actor creator sg observer origin cut state next returned Hforeign Hvalid Heffect.
  destruct Heffect.
  - eapply sem_pend_creator_publication_effect_receipt; eassumption.
  - eapply sem_pend_dispatch_framed_step_receipt with (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + apply MutexDelCreatorSourceAllocation; constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
  - eapply sem_pend_dispatch_framed_step_receipt with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + apply MutexDelCreatorSourceAllocation; constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
  - eapply sem_pend_dispatch_framed_step_receipt with
      (action := event_create_private_store_client actor eid allocation field stored).
    + apply MutexDelCreatorSourceStore.
    + exact Hforeign.
    + intros; discriminate.
    + split; [exact H0|reflexivity].
    + reflexivity.
    + apply TmrTaskCallNontimer; [constructor|split; [exact H0|reflexivity]].
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
Qed.

Lemma sem_pend_creator_publication_fields_guarantee : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local creator,
  mutex_del_creator_arguments creator ->
  kernel_client_fields_resource_guarantee (sem_pend_creator_fields_resources abi local)
    (mutex_del_creator_publication_step creator) (mutex_del_creator_publication_effect creator).
Proof.
  intros external platform port abi local creator Hargs sg cut before next after state frame Hstep Hpre.
  destruct Hstep.
  - exists (os_int_enter_state state); split; [constructor|].
    eapply kernel_client_int_enter_continuation_fields_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [constructor|].
    eapply kernel_client_int_exit_continuation_fields_resources; eassumption.
  - assert (Hbuiltin : @kernel_client_heap_step Z (fun _ _ _ _ _ => False) sg
      (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after) by (constructor; exact H).
    destruct (kernel_client_builtin_fields_resource_guarantee_proof external platform port Z abi local
      sg (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after state frame Hbuiltin Hpre)
      as [returned [Heffect Hpost]].
    exists returned; split; [|exact Hpost]. inversion Heffect; subst; [constructor; assumption|contradiction].
  - destruct (sem_pend_creator_publication_fields_extra external platform port abi local creator Hargs
      sg cut before next after state frame H Hpre) as [returned [Heffect Hpost]].
    exists returned; split; [constructor; exact Heffect|exact Hpost].
Qed.

Lemma sem_pend_creator_interrupt_fields_guarantee : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local creator,
  mutex_del_creator_arguments creator ->
  kernel_client_fields_resource_guarantee (sem_pend_creator_fields_resources abi local)
    (mutex_del_creator_interrupt_step creator) (mutex_del_creator_interrupt_effect creator).
Proof.
  intros external platform port abi local creator Hargs sg cut before next after state frame Hstep Hpre.
  destruct Hstep.
  - exists (os_int_enter_state state); split; [constructor|].
    eapply kernel_client_int_enter_continuation_fields_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [constructor|].
    eapply kernel_client_int_exit_continuation_fields_resources; eassumption.
  - assert (Hbuiltin : @kernel_client_heap_step Z (fun _ _ _ _ _ => False) sg
      (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after) by (constructor; exact H).
    destruct (kernel_client_builtin_fields_resource_guarantee_proof external platform port Z abi local
      sg (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after state frame Hbuiltin Hpre)
      as [returned [Heffect Hpost]].
    exists returned; split; [|exact Hpost]. inversion Heffect; subst; [constructor; assumption|contradiction].
  - destruct (sem_pend_creator_interrupt_fields_extra external platform port abi local creator Hargs
      sg cut before next after state frame H Hpre) as [returned [Heffect Hpost]].
    exists returned; split; [constructor; exact Heffect|exact Hpost].
Qed.

Lemma sem_pend_creator_publication_state_step_receipt :
  forall external port actor creator sg observer cut state next returned origin,
  actor <> Some observer -> kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned ->
  UCOS2_state_inv sg state ->
  kernel_client_heap_observer_cut observer next /\
  exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state false origin returned trace.
Proof.
  intros * Hforeign Hobserver Hstep Hvalid.
  pose proof (sem_pend_source_state_facts_from_valid sg state Hvalid) as Hfacts.
  destruct Hstep.
  - destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer
      KernelClientHeapClosed state KernelClientHeapClosed (os_int_enter_state state) origin Hforeign Hobserver
      ltac:(constructor) Hfacts) as [Hnext [trace Hreceipt]].
    split; [exact Hnext|]. eapply sem_pend_dispatch_client_receipt_inclusion;
      [intros action Hmember; apply MutexDelCreatorSourceAllocation; exact Hmember|exact Hreceipt].
  - destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer
      KernelClientHeapClosed state KernelClientHeapClosed
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) origin Hforeign Hobserver
      ltac:(constructor) Hfacts) as [Hnext [trace Hreceipt]].
    split; [exact Hnext|]. eapply sem_pend_dispatch_client_receipt_inclusion;
      [intros action Hmember; apply MutexDelCreatorSourceAllocation; exact Hmember|exact Hreceipt].
  - assert (Hallocated : kernel_client_heap_state_step mutex_del_creator_heap_effect sg
      (KernelClientHeapTaskPublication publication) state KernelClientHeapClosed
      (task_create_stack_publication_state sg publication state)) by (constructor; exact H).
    destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer
      (KernelClientHeapTaskPublication publication) state KernelClientHeapClosed _ origin Hforeign Hobserver
      Hallocated Hfacts) as [Hnext [trace Hreceipt]].
    split; [exact Hnext|]. eapply sem_pend_dispatch_client_receipt_inclusion;
      [intros action Hmember; apply MutexDelCreatorSourceAllocation; exact Hmember|exact Hreceipt].
  - split.
    + destruct H; [destruct H; exact I|exact I].
    + eapply sem_pend_creator_publication_effect_receipt; eassumption.
Qed.

Lemma sem_pend_creator_interrupt_state_step_receipt :
  forall external port actor creator sg observer cut state next returned origin,
  actor <> Some observer -> kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_state_step (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  UCOS2_state_inv sg state ->
  kernel_client_heap_observer_cut observer next /\
  exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state false origin returned trace.
Proof.
  intros * Hforeign Hobserver Hstep Hvalid.
  destruct Hstep.
  - eapply sem_pend_creator_publication_state_step_receipt; try eassumption; constructor.
  - eapply sem_pend_creator_publication_state_step_receipt; try eassumption; constructor.
  - eapply sem_pend_creator_publication_state_step_receipt; try eassumption; constructor; exact H.
  - split.
    + destruct H; try exact I. destruct H; [destruct H; exact I|exact I].
    + eapply sem_pend_creator_interrupt_effect_receipt; eassumption.
Qed.

(** Interpret each actual public or private C step while its input owner
    and returned owner are still available. The nil case and every private
    endpoint remain in these original traces. *)
Lemma sem_pend_creator_publication_fields_trace_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local actor creator sg observer cut before next after (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (sem_pend_creator_fields_resources abi local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state false origin returned trace) /\
    kernel_client_heap_observer_cut observer next /\
    (sem_pend_creator_fields_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port abi local actor creator sg observer cut before next after frame Hforeign Hargs Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state; split; [constructor|]. split.
    + exists (@KernelClientTaskSourceNil external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state); constructor.
    + split; assumption.
  - pose proof (sem_pend_creator_fields_resources_valid external platform port abi local sg
      cut state before frame Hpre) as Hvalid.
    destruct (sem_pend_creator_publication_fields_guarantee external platform port abi local creator Hargs sg
      cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    destruct (sem_pend_creator_publication_state_step_receipt external port actor creator sg observer cut state
      middle_cut middle_state origin Hforeign Hobserver Hstep Hvalid) as [Hmiddle_observer [head Hhead]].
    destruct (IHHtrace middle_state origin Hmiddle_observer Hmiddle)
      as [returned [Htail [[tail Htail_receipt] [Hfinal Hpost]]]].
    exists returned; split; [econstructor; eassumption|]. split; [|split; assumption].
    exact (sem_pend_dispatch_client_receipt_append external port
      (mutex_del_creator_source_client actor creator) sg observer None origin state false origin middle_state
      head Hhead false origin returned tail Htail_receipt).
Qed.

Lemma sem_pend_creator_interrupt_fields_trace_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local actor creator sg observer cut before next after (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (sem_pend_creator_fields_resources abi local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state false origin returned trace) /\
    kernel_client_heap_observer_cut observer next /\
    (sem_pend_creator_fields_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port abi local actor creator sg observer cut before next after frame Hforeign Hargs Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state; split; [constructor|]. split.
    + exists (@KernelClientTaskSourceNil external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state); constructor.
    + split; assumption.
  - pose proof (sem_pend_creator_fields_resources_valid external platform port abi local sg
      cut state before frame Hpre) as Hvalid.
    destruct (sem_pend_creator_interrupt_fields_guarantee external platform port abi local creator Hargs sg
      cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    destruct (sem_pend_creator_interrupt_state_step_receipt external port actor creator sg observer cut state
      middle_cut middle_state origin Hforeign Hobserver Hstep Hvalid) as [Hmiddle_observer [head Hhead]].
    destruct (IHHtrace middle_state origin Hmiddle_observer Hmiddle)
      as [returned [Htail [[tail Htail_receipt] [Hfinal Hpost]]]].
    exists returned; split; [econstructor; eassumption|]. split; [|split; assumption].
    exact (sem_pend_dispatch_client_receipt_append external port
      (mutex_del_creator_source_client actor creator) sg observer None origin state false origin middle_state
      head Hhead false origin returned tail Htail_receipt).
Qed.

(** The finite receipt is immediately produced at the same real
    allocation/initializer factory used by the original creator. Both the
    empty return and the nonempty publication branch are retained. *)
Lemma sem_pend_creator_publication_fields_produces_closed :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local actor creator sg observer state origin before (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world abi local sg state ** frame) before ->
  exists returned after,
    kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg
      KernelClientHeapClosed before KernelClientHeapClosed after /\
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    (exists trace : kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state false origin returned trace) /\
    (kernel_client_continuation_fields_world abi local sg returned ** frame) after.
Proof.
  intros external platform port abi local actor creator sg observer state origin before frame Hforeign Hargs Hbinding Hpre.
  destruct (sem_pend_allocation_fields_produces_receipt external platform port abi local actor sg observer origin state
      before frame Hforeign Hbinding Hpre) as [cut [popped [allocated [Hallocate [Hstate [Hreceipt Hpending]]]]]].
  destruct (sem_pend_creator_allocate_fields_pending external platform port abi local sg state before cut popped frame
      Hallocate Hpre) as [first [Heffect Hfirst]].
  assert (Hfinish : exists after, kernel_client_heap_trace (mutex_del_creator_publication_step creator)
    sg cut popped KernelClientHeapClosed after).
  { destruct Heffect.
    - exists popped; constructor.
    - destruct (sem_pend_creator_initialization_fields_publish external platform port abi local sg creator
        (event_pool_addr sg eid) returned popped frame Hargs Hfirst)
        as [actual [allocation [initialized [final [after [Hpointer [Hget [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
      exists after; eapply KernelClientHeapTraceCons.
      + apply KernelClientHeapRegistered; apply MutexDelCreatorPublicationFinish; exact Hrun.
      + constructor. }
  destruct Hfinish as [after Hfinish].
  assert (Htrace : kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg
    KernelClientHeapClosed before KernelClientHeapClosed after).
  { eapply KernelClientHeapTraceCons.
    - apply KernelClientHeapRegistered; apply MutexDelCreatorPublicationAllocate; exact Hallocate.
    - exact Hfinish. }
  destruct (sem_pend_creator_publication_fields_trace_receipt external platform port abi local actor creator sg observer
    KernelClientHeapClosed before KernelClientHeapClosed after frame Hforeign Hargs Htrace state origin I Hpre)
    as [returned [Hstates [Hcalls [_ Hpost]]]].
  exists returned, after; repeat split; assumption.
Qed.
