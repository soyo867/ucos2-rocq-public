Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event_pool Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_borrow_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_allocation_source_spec.
Import UCOS2_C_Rules KernelHeapObservation EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A creator's actual private cut in the ALREADY established focused
    world. The descriptor of the suspended Del invocation is kept, not
    forgotten and later reconstructed from a weak capsule map. *)
Definition mutex_del_creator_call_stack_pending {external platform port}
  (abi : Armv7aContinuationABI external platform port) focus payload sg pointer state : Assertion :=
  EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
    (kernel_client_call_stack_world abi sg focus payload state ** event_private_storage_rep sg eid allocation).

Lemma mutex_del_creator_call_stack_allocate : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload sg state before cut after
  (frame : Assertion),
  mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after ->
  (kernel_client_call_stack_world abi sg focus payload state ** frame) before ->
  exists returned,
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut returned ** frame) after.
Proof.
  intros external platform port abi focus payload sg state before cut after frame Hsource Hpre.
  assert (Hopen : kernel_client_call_stack_world abi sg focus payload state ** frame |--
    coq_prop (kernel_client_call_stack_facts focus payload state) &&
    (kernel_program_inv sg state **
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_call_stack_world; entailer!. }
  destruct (Hopen before Hpre) as [Hfocus Howned].
  destruct Hsource as [heap Hbinding Hread|before pointer next after Hbinding Hnonzero Hread Hnext Hwrites].
  - destruct (event_create_allocate_heap_source sg state heap _ Hbinding Howned)
      as [result [allocated [produced [Hhead [Hstep [Hrun Hpost]]]]]].
    pose proof (pointer_load_deterministic _ _ _ _ Hread Hhead) as Hpointer.
    destruct result as [[eid image]|].
    + destruct Hrun as [Hnonzero _]; cbn [event_create_return_ptr] in Hpointer.
      exfalso; apply Hnonzero; symmetry; exact Hpointer.
    + destruct (event_create_allocate_critical_empty_frame _ _ Hstep) as [_ ->].
      exists state; split; [constructor; exact Hstep|exact Hpre].
  - destruct (event_create_allocate_heap_source sg state before _ Hbinding Howned)
      as [result [allocated [produced [Hhead [Hstep [Hrun Hpost]]]]]].
    pose proof (pointer_load_deterministic _ _ _ _ Hread Hhead) as Hpointer.
    destruct result as [[eid image]|].
    + cbn [event_create_return_ptr] in Hpointer.
      destruct Hrun as [Hpositive [actual_next [Hnext_read Hwrite]]].
      assert (next = actual_next).
      { rewrite Hpointer in Hnext; eapply pointer_load_deterministic; eassumption. }
      subst actual_next.
      assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
      pose proof (event_create_allocate_critical_task_frame _ _ _ Hstep) as Htasks.
      pose proof (proj2 (event_create_allocate_critical_private_result state eid image allocated Hstep)) as Hlookup.
      exists allocated; split.
      * rewrite Hpointer; econstructor; exact Hstep.
      * assert (Hmerge : kernel_program_inv sg allocated **
          event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
          (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) |--
          kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
            sg focus payload (KernelClientHeapExtra pointer) allocated ** frame).
        { cbn [kernel_client_call_stack_resources]; unfold mutex_del_creator_call_stack_pending.
          Exists eid (sem_create_allocation_identity state image).
          unfold kernel_client_call_stack_world, kernel_client_call_stack_facts in *.
          rewrite Htasks; cbn [sem_create_allocation_identity eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
        exact (Hmerge after Hpost).
    + cbn [event_create_return_ptr] in Hpointer; exfalso; apply Hnonzero; exact Hpointer.
Qed.

(** The physical publication rule consumes initialized private bytes once;
    the Task map is unchanged, hence every retained call descriptor and
    its frame/SP index still refers to the same task generation. *)
Lemma mutex_del_creator_call_stack_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload sg creator state eid allocation image,
  UCOS2_state_inv sg state ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  mutex_del_creator_arguments creator ->
  allocation.(eventPrivateStorage) = event_create_stores_image image (mutex_del_creator_fields sg creator) ->
  event_private_storage_rep sg eid allocation ** kernel_client_call_stack_world abi sg focus payload state |--
    kernel_client_call_stack_world abi sg focus payload (mutex_del_creator_published_state creator state eid allocation).
Proof.
  intros external platform port abi focus payload sg creator state eid allocation image
    Hvalid Hget Hqueue Hpcp Hargs Himage.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { pose proof Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hmerge : event_private_storage_rep sg eid allocation **
    (event_raw_rep sg state.(TskState) state.(EventState) ** queue_storage_rep sg state.(EventState) **
      UCOS2_raw_rep_missing_event_queue sg state) |--
    UCOS2_inv sg (mutex_del_creator_published_state creator state eid allocation)).
  { destruct creator; cbn [mutex_del_creator_fields mutex_del_creator_arguments] in Hargs, Himage;
      rewrite event_create_stores_image_initialization_eq in Himage;
      unfold mutex_del_creator_published_state; cbn [mutex_del_creator_event].
    - eapply sem_create_publish_merge; try eassumption; [lia|apply event_name_valid_disabled; exact Hnames].
    - eapply mbox_create_publish_merge; try eassumption; apply event_name_valid_disabled; exact Hnames. }
  assert (Hopen : event_private_storage_rep sg eid allocation **
      kernel_client_call_stack_world abi sg focus payload state |--
    coq_prop (kernel_client_call_stack_facts focus payload state) &&
    ((event_private_storage_rep sg eid allocation **
      (event_raw_rep sg state.(TskState) state.(EventState) **
       queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state)) **
     (unmap_table_rep sg ** armv7a_task_call_stacks abi state.(TskState) focus
       state.(TskState).(parkedTaskStacks)))).
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap.
    rewrite (UCOS2_inv_split_event_queue sg state); Intros; entailer!. }
  intros heap Hpre; destruct (Hopen heap Hpre) as [Hfocus [owned [rest [Hjoin [Howned Hrest]]]]].
  assert (Hclose : UCOS2_inv sg (mutex_del_creator_published_state creator state eid allocation) **
      (unmap_table_rep sg ** armv7a_task_call_stacks abi state.(TskState) focus
        state.(TskState).(parkedTaskStacks)) |--
    kernel_client_call_stack_world abi sg focus payload (mutex_del_creator_published_state creator state eid allocation)).
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap.
    unfold kernel_client_call_stack_facts in *.
    unfold mutex_del_creator_published_state; cbn [replace_EventS TskState]; entailer!. }
  apply (Hclose heap); exists owned, rest; split; [exact Hjoin|].
  split; [exact (Hmerge owned Howned)|exact Hrest].
Qed.

Lemma mutex_del_creator_call_stack_initialization : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload sg creator pointer state before
  (frame : Assertion),
  mutex_del_creator_arguments creator ->
  (mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame) before ->
  exists eid allocation initialized final after,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    event_create_private_stores eid (mutex_del_creator_fields sg creator) state tt initialized /\
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after /\
    (kernel_client_call_stack_world abi sg focus payload
      (mutex_del_creator_published_state creator initialized eid final) ** frame) after.
Proof.
  intros external platform port abi focus payload sg creator pointer state before frame Hargs Hpre.
  assert (Hopen : mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        UCOS2_state_inv sg state /\ kernel_client_call_stack_facts focus payload state) &&
      (event_private_storage_rep sg eid allocation ** kernel_program_inv sg state **
        (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_creator_call_stack_pending; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_call_stack_world, kernel_program_inv; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp [Hvalid Hfocus]]]]] Howned]]].
  destruct (event_create_private_prefix_heap sg eid (mutex_del_creator_fields sg creator) state allocation
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
  assert (Hclose : event_private_storage_rep sg eid final ** kernel_program_inv sg initialized **
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_call_stack_world abi sg focus payload
      (mutex_del_creator_published_state creator initialized eid final) ** frame).
  { rewrite <- Htasks.
    assert (Hgroup : event_private_storage_rep sg eid final ** kernel_program_inv sg initialized **
        (armv7a_task_call_stacks abi initialized.(TskState) focus initialized.(TskState).(parkedTaskStacks) ** frame) |--
      (event_private_storage_rep sg eid final ** kernel_client_call_stack_world abi sg focus payload initialized) ** frame).
    { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts in *; rewrite Htasks; entailer!. }
    intros heap Hheap; destruct (Hgroup heap Hheap) as [owned [rest [Hjoin [Hgroup_owned Hrest]]]].
    exists owned, rest; split; [exact Hjoin|]. split; [|exact Hrest].
    exact (mutex_del_creator_call_stack_publish external platform port abi focus payload sg creator initialized
      eid final allocation.(eventPrivateStorage) Hinitialized Hfinal ltac:(congruence) ltac:(congruence)
      Hargs Himage owned Hgroup_owned). }
  exists eid, allocation, initialized, final, after.
  split; [exact Hpointer|]. split; [exact Hget|]. split; [exact Hstores|]. split; [exact Hfinal|].
  split; [rewrite Hpointer; exact Hwrites|exact (Hclose after Hafter)].
Qed.

Lemma mutex_del_creator_call_stack_extension : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator,
  mutex_del_creator_arguments creator ->
  kernel_client_call_stack_extension_valid abi (mutex_del_creator_call_stack_pending abi focus payload)
    focus payload (mutex_del_creator_publication_step creator) (mutex_del_creator_publication_effect creator).
Proof.
  intros external platform port abi focus payload creator Hargs sg cut before next after state frame Hsource Hpre.
  destruct Hsource as [before cut after Hallocate|pointer before after Hwrites].
  - destruct (mutex_del_creator_call_stack_allocate external platform port abi focus payload sg state before cut
      after frame Hallocate Hpre) as [returned [Hstep Hafter]].
    exists returned; split; [constructor; exact Hstep|exact Hafter].
  - destruct (mutex_del_creator_call_stack_initialization external platform port abi focus payload sg creator pointer
      state before frame Hargs Hpre) as [eid [allocation [initialized [final [produced
        [Hpointer [Hget [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    exists (mutex_del_creator_published_state creator initialized eid final).
    split; [econstructor; eassumption|exact Hafter].
Qed.

(** The actual heap trace and logical history have one common returned
    state. Built-in counter/TCB producers are reused, not re-proved. This
    retains the focus until an actual selection consumes it; no full Save
    or arbitrary handler-return claim is made by this trace theorem. *)
Lemma mutex_program_creator_call_stack_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload initial creator sg cut before next after
  (frame : Assertion),
  mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  forall state,
  mutex_program_reachable initial sg state ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
    sg focus payload cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    mutex_program_reachable initial sg returned /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned ** frame) after.
Proof.
  intros external platform port abi focus payload initial creator sg cut before next after frame Hargs Htrace.
  induction Htrace; intros state Hreachable Hpre.
  - exists state; split; [constructor|]; split; assumption.
  - destruct (kernel_client_call_stack_step_resources external platform port Z abi
      (mutex_del_creator_call_stack_pending abi focus payload) focus payload
      (mutex_del_creator_publication_step creator) (mutex_del_creator_publication_effect creator)
      (mutex_del_creator_call_stack_extension external platform port abi focus payload creator Hargs)
      sg cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    assert (Hmiddle_history : mutex_program_reachable initial sg middle_state).
    { eapply mutex_program_creator_state_trace; [exact Hreachable|].
      econstructor; [exact Hstep|constructor]. }
    destruct (IHHtrace middle_state Hmiddle_history Hmiddle) as [returned [Htail [Hreachable_returned Hpost]]].
    exists returned; split; [econstructor; eassumption|]; split; assumption.
Qed.

(** This is the projection of the concrete heap registry above, not a
    restriction of the configured program's complete client family. The
    final theorem embeds this actual trace into that family explicitly.
    Other allowed clients keep their separate physical source producers. *)
Inductive mutex_del_creator_source_client (actor : option nat) (creator : MutexDelSimpleCreator)
  : KernelClientAction -> Prop :=
| MutexDelCreatorSourceAllocation : forall action,
    mutex_del_allocation_source_client actor action -> mutex_del_creator_source_client actor creator action
| MutexDelCreatorSourceStore : forall eid allocation field stored,
    mutex_del_creator_source_client actor creator
      (event_create_private_store_client actor eid allocation field stored)
| MutexDelCreatorSourcePublish : forall eid allocation,
    mutex_del_creator_source_client actor creator
      (event_create_publication_client actor eid allocation (mutex_del_creator_event creator allocation)).

Lemma mutex_del_creator_stores_resumption_source : forall external port actor creator sg observer origin
  eid writes state result returned,
  actor <> Some observer ->
  event_create_private_stores eid writes state result returned ->
  kernel_resumption_task_source_trace external port (mutex_del_creator_source_client actor creator)
    sg observer None origin state false origin returned.
Proof.
  intros external port actor creator sg observer origin eid writes.
  induction writes as [|[field stored] rest IH]; intros state result returned Hforeign Hstores.
  - destruct Hstores as [_ ->]; constructor.
  - destruct Hstores as [allocation [Hget Htail]].
    change false with (orb false false).
    eapply kernel_resumption_task_source_trace_trans with (middle := origin)
      (transient := replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state)
      (stopped1 := false) (stopped2 := false).
    + change (kernel_resumption_task_source_trace external port (mutex_del_creator_source_client actor creator)
        sg observer None origin state
        (kernel_client_stops (event_create_private_store_client actor eid allocation field stored) observer)
        origin (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state)).
      eapply kernel_client_framed_step_resumption_source with
        (action := event_create_private_store_client actor eid allocation field stored).
      * apply MutexDelCreatorSourceStore.
      * exact Hforeign.
      * intros; discriminate.
      * split; [exact Hget|reflexivity].
      * reflexivity.
      * reflexivity.
    + eapply IH; eassumption.
Qed.

Lemma mutex_del_creator_publication_extension_source : forall external port actor creator sg observer,
  actor <> Some observer ->
  sg.(osKernelConfig).(cfgEventNames) = false ->
  kernel_client_heap_extension_source external port (mutex_del_creator_source_client actor creator)
    sg observer None (mutex_del_creator_publication_effect creator).
Proof.
  intros external port actor creator sg observer Hforeign Hnames cut state next returned origin
    Hcompatible Heffect.
  destruct Heffect as [cut state returned Hallocate|pointer state eid allocation initialized final
    Hpointer Hget Hstores Hfinal].
  - destruct Hallocate; split; try exact I; exists false, origin;
      eapply kernel_resumption_task_source_trace_inclusion.
    + intros action Hin; constructor; exact Hin.
    + eapply mutex_del_allocate_resumption_source; eassumption.
    + intros action Hin; constructor; exact Hin.
    + eapply mutex_del_allocate_resumption_source; eassumption.
  - split; [exact I|]. exists false, origin.
    change false with (orb false false).
    eapply kernel_resumption_task_source_trace_trans with (middle := origin) (transient := initialized)
      (stopped1 := false) (stopped2 := false).
    + eapply mutex_del_creator_stores_resumption_source; eassumption.
    + change (kernel_resumption_task_source_trace external port (mutex_del_creator_source_client actor creator)
        sg observer None origin initialized
        (kernel_client_stops (event_create_publication_client actor eid final
          (mutex_del_creator_event creator final)) observer)
        origin (mutex_del_creator_published_state creator initialized eid final)).
      eapply kernel_client_framed_step_resumption_source with
        (action := event_create_publication_client actor eid final (mutex_del_creator_event creator final)).
      * apply MutexDelCreatorSourcePublish.
      * exact Hforeign.
      * intros; discriminate.
      * split; [exact Hfinal|]. split; [apply event_name_valid_disabled; exact Hnames|reflexivity].
      * reflexivity.
      * reflexivity.
Qed.

Lemma mutex_del_creator_source_trace_nonstopping : forall external port actor creator sg observer event_observer
  origin state stopped returned_origin returned,
  kernel_resumption_task_source_trace external port (mutex_del_creator_source_client actor creator)
    sg observer event_observer origin state stopped returned_origin returned -> stopped = false.
Proof.
  intros external port actor creator sg observer event_observer origin state stopped returned_origin returned Htrace.
  assert (Hsegment : forall origin state stopped returned_origin returned,
    kernel_client_task_source_trace external port (mutex_del_creator_source_client actor creator)
      sg observer event_observer origin state stopped returned_origin returned -> stopped = false).
  { intros first before stop last after Hsegment.
    induction Hsegment as [base_origin base_state|action first before middle transient last after stop_value
      Hregistered Hactor Hevent Hstep Hsource Htail IH].
    - reflexivity.
    - rewrite IH; destruct Hregistered; [destruct H| | ]; reflexivity. }
  induction Htrace as [origin state|first before stopped1 middle transient stopped2 last after
    Hfirst Htimer Htail IH].
  - reflexivity.
  - rewrite (Hsegment _ _ _ _ _ Hfirst), IH; reflexivity.
Qed.

Lemma mutex_del_creator_call_stack_resources_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload cut state (frame : Assertion),
  kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
    sg focus payload cut state ** frame |-- coq_prop (UCOS2_state_inv sg state) && TT.
Proof.
  intros; destruct cut; cbn [kernel_client_call_stack_resources].
  - unfold kernel_client_call_stack_world, kernel_program_inv; entailer!.
  - unfold kernel_client_call_stack_publication; entailer!.
  - unfold mutex_del_creator_call_stack_pending; Intros eid allocation.
    unfold kernel_client_call_stack_world, kernel_program_inv; entailer!.
Qed.

(** A SAME-edge source join: concrete heap trace, strong pending call,
    private creator bytes, reachable program history, and registered source
    trace have one returned state. The stable selected profile is recovered
    from the actual owned world; it is not another public Require atom.
    This does not yet supply a CPU return or a full Save/Restore contract. *)
Lemma mutex_program_creator_call_stack_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients actor creator initial
  sg observer origin focus payload cut before next after (frame : Assertion) state,
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer ->
  mutex_del_creator_arguments creator ->
  mutex_program_reachable initial sg state ->
  kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
    sg focus payload cut state ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer None
      origin state false returned_origin returned /\
    mutex_program_reachable initial sg returned /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned ** frame) after.
Proof.
  intros external platform port abi clients actor creator initial sg observer origin focus payload cut before
    next after frame state Hinclude Hforeign Hargs Hreachable Hcompatible Htrace Hpre.
  pose proof (mutex_del_creator_call_stack_resources_valid external platform port abi sg focus payload cut state
    frame before Hpre) as [Hvalid _].
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { pose proof Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  destruct (kernel_client_call_stack_trace_source_resources external platform port Z abi
    (mutex_del_creator_call_stack_pending abi focus payload) focus payload
    (mutex_del_creator_publication_step creator) (mutex_del_creator_publication_effect creator)
    (mutex_del_creator_source_client actor creator) sg observer None
    (mutex_del_creator_call_stack_extension external platform port abi focus payload creator Hargs)
    ltac:(constructor; constructor) ltac:(intros; constructor; constructor)
    ltac:(intros; constructor; constructor)
    (mutex_del_creator_publication_extension_source external port actor creator sg observer Hforeign Hnames)
    cut before next after frame Htrace state origin Hcompatible Hpre)
    as [returned [stopped [returned_origin [Hlogical [Hsource [Hnext Hpost]]]]]].
  pose proof (mutex_del_creator_source_trace_nonstopping external port actor creator sg observer None
    origin state stopped returned_origin returned Hsource) as ->.
  exists returned, returned_origin; split; [exact Hlogical|]. split.
  - eapply kernel_resumption_task_source_trace_inclusion; eassumption.
  - split; [eapply mutex_program_creator_state_trace; eassumption|]. split; assumption.
Qed.
