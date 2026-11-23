Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.event Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_type_loan_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Import UCOS2_C_Rules EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual selected-profile creator programs. Their C arguments determine
    both the physical initializer and the published abstract payload. Queue
    creation has a QCB stage and another Restore and is NOT this program.
    A creator's public call may be interrupted between these fragments;
    this owner proves only a supplied uninterrupted initialization segment. *)
Inductive MutexDelSimpleCreator : Type :=
| MutexDelSemCreator (count : Z)
| MutexDelMboxCreator (message : Z).

Definition mutex_del_creator_arguments (creator : MutexDelSimpleCreator) : Prop :=
  match creator with
  | MutexDelSemCreator count => 0 <= count < 65536
  | MutexDelMboxCreator message => 0 <= message < 4294967296
  end.

Definition mutex_del_creator_fields sg (creator : MutexDelSimpleCreator) :=
  match creator with
  | MutexDelSemCreator count =>
      event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 3 count 0 0
  | MutexDelMboxCreator message =>
      event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 1 0 message 0
  end.

Definition mutex_del_creator_event (creator : MutexDelSimpleCreator) allocation :=
  match creator with
  | MutexDelSemCreator count => sem_create_event allocation count 0
  | MutexDelMboxCreator message => mbox_create_event allocation message 0
  end.

Definition mutex_del_creator_published_state creator state eid allocation :=
  replace_EventS (event_publish state.(EventState) eid (mutex_del_creator_event creator allocation)) state.

(** The two metadata facts come from the concrete allocator. They do not
    constrain a user pointer or promise a future postcondition. In contrast
    with an arbitrary private ECB, this pending client has acquired neither
    a QCB nor a Mutex priority lease. Its complete physical bytes are owned. *)
Definition mutex_del_creator_pending {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg pointer state : Assertion :=
  EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
    (kernel_client_heap_world abi sg state ** event_private_storage_rep sg eid allocation).

Lemma mutex_del_creator_fields_in_range : forall sg creator,
  mutex_del_creator_arguments creator ->
  Forall (fun write => In (fst write) (event_fields sg.(osKernelConfig).(cfgEventNames)) /\
    event_create_field_value_in_range (fst write) (snd write)) (mutex_del_creator_fields sg creator).
Proof.
  intros sg creator Hargs; destruct creator; cbn [mutex_del_creator_fields mutex_del_creator_arguments] in *;
    apply event_create_initialization_fields_in_range; lia.
Qed.

(** Publication is resource reindexing AFTER the actual final store. It
    consumes the private ECB once into the public Event owner, with the
    same table and full capsule map. The image equality is derived from
    the actual field execution by the following producer. *)
Lemma mutex_del_creator_publish_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg creator state eid allocation image,
  UCOS2_state_inv sg state ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  mutex_del_creator_arguments creator ->
  allocation.(eventPrivateStorage) = event_create_stores_image image (mutex_del_creator_fields sg creator) ->
  event_private_storage_rep sg eid allocation ** kernel_client_heap_world abi sg state |--
    kernel_client_heap_world abi sg (mutex_del_creator_published_state creator state eid allocation).
Proof.
  intros external platform port abi sg creator state eid allocation image Hvalid Hget Hqueue Hpcp Hargs Himage.
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
  assert (Hopen : event_private_storage_rep sg eid allocation ** kernel_client_heap_world abi sg state |--
    ((event_private_storage_rep sg eid allocation **
      (event_raw_rep sg state.(TskState) state.(EventState) **
       queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state)) **
      (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks)))).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap.
    rewrite (UCOS2_inv_split_event_queue sg state); Intros; entailer!. }
  assert (Hclose : UCOS2_inv sg (mutex_del_creator_published_state creator state eid allocation) **
      (unmap_table_rep sg ** armv7a_task_continuations abi state.(TskState).(parkedTaskStacks)) |--
    kernel_client_heap_world abi sg (mutex_del_creator_published_state creator state eid allocation)).
  { unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap.
    unfold mutex_del_creator_published_state; cbn [replace_EventS TskState]; entailer!. }
  intros heap Hpre; apply (Hclose heap).
  destruct (Hopen heap Hpre) as [owned [rest [Hjoin [Howned Hrest]]]].
  exists owned, rest; split; [exact Hjoin|]. split; [exact (Hmerge owned Howned)|exact Hrest].
Qed.

(** A real source producer, not a certificate substituted for bytes.
    The field list includes Type/Cnt/Ptr and the actual WaitListInit byte
    stores. The final logical publication adds no physical write. *)
Lemma mutex_del_creator_initialization_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg creator pointer state before (frame : Assertion),
  mutex_del_creator_arguments creator ->
  (mutex_del_creator_pending abi sg pointer state ** frame) before ->
  exists eid allocation initialized final after,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    event_create_private_stores eid (mutex_del_creator_fields sg creator) state tt initialized /\
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after /\
    (kernel_client_heap_world abi sg (mutex_del_creator_published_state creator initialized eid final) ** frame) after.
Proof.
  intros external platform port abi sg creator pointer state before frame Hargs Hpre.
  assert (Hopen : mutex_del_creator_pending abi sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        UCOS2_state_inv sg state) &&
      (event_private_storage_rep sg eid allocation ** kernel_program_inv sg state **
        (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_creator_pending; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_heap_world, kernel_program_inv; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp Hvalid]]]] Howned]]].
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
      (armv7a_task_continuations abi state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_heap_world abi sg (mutex_del_creator_published_state creator initialized eid final) ** frame).
  { rewrite <- Htasks.
    assert (Hgroup : event_private_storage_rep sg eid final ** kernel_program_inv sg initialized **
        (armv7a_task_continuations abi initialized.(TskState).(parkedTaskStacks) ** frame) |--
      ((event_private_storage_rep sg eid final ** kernel_client_heap_world abi sg initialized) ** frame)).
    { unfold kernel_client_heap_world; entailer!. }
    intros heap Hheap; destruct (Hgroup heap Hheap) as [owned [rest [Hjoin [Hgroup_owned Hrest]]]].
    exists owned, rest; split; [exact Hjoin|]. split; [|exact Hrest].
    exact (mutex_del_creator_publish_resources external platform port abi sg creator initialized
      eid final allocation.(eventPrivateStorage) Hinitialized Hfinal ltac:(congruence) ltac:(congruence)
      Hargs Himage owned Hgroup_owned). }
  exists eid, allocation, initialized, final, after.
  split; [exact Hpointer|]. split; [exact Hget|]. split; [exact Hstores|]. split; [exact Hfinal|].
  split; [rewrite Hpointer; exact Hwrites|exact (Hclose after Hafter)].
Qed.

Inductive mutex_del_creator_publication_step (creator : MutexDelSimpleCreator) (sg : StableGlobVars) :
  KernelClientHeapCut Z -> model -> KernelClientHeapCut Z -> model -> Prop :=
| MutexDelCreatorPublicationAllocate : forall before cut after,
    mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after ->
    mutex_del_creator_publication_step creator sg KernelClientHeapClosed before cut after
| MutexDelCreatorPublicationFinish : forall pointer before after,
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after ->
    mutex_del_creator_publication_step creator sg (KernelClientHeapExtra pointer) before KernelClientHeapClosed after.

Inductive mutex_del_creator_publication_effect (creator : MutexDelSimpleCreator) (sg : StableGlobVars) :
  KernelClientHeapCut Z -> UCOS2_Verify_State -> KernelClientHeapCut Z -> UCOS2_Verify_State -> Prop :=
| MutexDelCreatorPublicationAllocateState : forall cut state returned,
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned ->
    mutex_del_creator_publication_effect creator sg KernelClientHeapClosed state cut returned
| MutexDelCreatorPublicationFinishState : forall pointer state eid allocation initialized final,
    pointer = event_pool_addr sg eid ->
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    event_create_private_stores eid (mutex_del_creator_fields sg creator) state tt initialized ->
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
    mutex_del_creator_publication_effect creator sg (KernelClientHeapExtra pointer) state KernelClientHeapClosed
      (mutex_del_creator_published_state creator initialized eid final).

(** The new stage is supplyable by the EXISTING actual free-pop. No
    private image is made from the Closed world by definition alone. *)
Lemma mutex_del_creator_allocate_pending : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state before cut after (frame : Assertion),
  mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after ->
  (kernel_client_heap_world abi sg state ** frame) before ->
  exists returned,
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut returned ** frame) after.
Proof.
  intros external platform port abi sg state before cut after frame Hsource Hpre.
  destruct (mutex_del_creator_heap_extension_valid external platform port abi sg KernelClientHeapClosed
    before cut after state frame Hsource Hpre) as [returned [Hstep Hafter]].
  exists returned; split; [exact Hstep|]. destruct Hstep.
  - exact Hafter.
  - pose proof (proj2 (event_create_allocate_critical_private_result state eid image returned H)) as Hget.
    assert (Hclose : kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg
        (KernelClientHeapExtra (event_pool_addr sg eid)) returned ** frame |--
      kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg
        (KernelClientHeapExtra (event_pool_addr sg eid)) returned ** frame).
    { cbn [kernel_client_heap_resources]; unfold mutex_del_creator_heap_resources; Intros found allocation.
      assert (Hbindings : event_pool_addr sg eid = event_pool_addr sg found /\
        returned.(EventState).(eventLifecycle).(eventPrivate) found = Some allocation) by tauto.
      destruct Hbindings as [Haddress Hlookup].
      assert (found = eid) by (apply event_pool_addr_injective with (sg := sg); congruence); subst found.
      assert (allocation = sem_create_allocation_identity state image) by (unfold sem_create_allocation_identity; congruence).
      subst allocation; unfold mutex_del_creator_pending; Exists eid (sem_create_allocation_identity state image).
      cbn [sem_create_allocation_identity eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
    exact (Hclose after Hafter).
Qed.

Lemma mutex_del_creator_publication_extension_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator,
  mutex_del_creator_arguments creator ->
  kernel_client_heap_extension_valid abi (mutex_del_creator_pending abi)
    (mutex_del_creator_publication_step creator) (mutex_del_creator_publication_effect creator).
Proof.
  intros external platform port abi creator Hargs sg cut before next after state frame Hsource Hpre.
  destruct Hsource as [before cut after Hallocate|pointer before after Hwrites].
  - destruct (mutex_del_creator_allocate_pending external platform port abi sg state before cut after frame
      Hallocate Hpre) as [returned [Hstep Hafter]].
    exists returned; split; [constructor; exact Hstep|exact Hafter].
  - destruct (mutex_del_creator_initialization_publish external platform port abi sg creator pointer state before
      frame Hargs Hpre) as [eid [allocation [initialized [final [produced
        [Hpointer [Hget [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    exists (mutex_del_creator_published_state creator initialized eid final).
    split; [econstructor; eassumption|exact Hafter].
Qed.

(** Both free-list outcomes have a reachable Closed endpoint. In the
    nonempty case the path contains the real pop and every initializer
    store, then consumes the private image at publication. These are heap
    fragments; the intervening Restore/control path is a separate source
    obligation, not silently treated as an empty CPU instruction. *)
Lemma mutex_del_creator_publication_produces_closed : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg creator state before (frame : Assertion),
  mutex_del_creator_arguments creator -> sem_create_source_binding sg ->
  (kernel_client_heap_world abi sg state ** frame) before ->
  exists returned after,
    kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg
      KernelClientHeapClosed before KernelClientHeapClosed after /\
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    (kernel_client_heap_world abi sg returned ** frame) after.
Proof.
  intros external platform port abi sg creator state before frame Hargs Hbinding Hpre.
  destruct (mutex_del_creator_heap_produces_cut external platform port abi sg state before frame Hbinding Hpre)
    as [cut [popped [first [Hallocate [_ _]]]]].
  destruct (mutex_del_creator_allocate_pending external platform port abi sg state before cut popped frame
    Hallocate Hpre) as [allocated [Heffect Hpending]].
  assert (Hfinish : exists after, kernel_client_heap_trace (mutex_del_creator_publication_step creator)
    sg cut popped KernelClientHeapClosed after).
  { destruct Heffect.
    - exists popped; constructor.
    - destruct (mutex_del_creator_initialization_publish external platform port abi sg creator
        (event_pool_addr sg eid) returned popped frame Hargs Hpending)
        as [actual [allocation [initialized [final [after [Hpointer [Hget [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
      exists after; eapply KernelClientHeapTraceCons.
      + apply KernelClientHeapRegistered; constructor; exact Hrun.
      + constructor. }
  destruct Hfinish as [after Hfinish].
  assert (Htrace : kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg
    KernelClientHeapClosed before KernelClientHeapClosed after).
  { eapply KernelClientHeapTraceCons; [apply KernelClientHeapRegistered; constructor; exact Hallocate|exact Hfinish]. }
  destruct (kernel_client_heap_trace_resources external platform port Z abi (mutex_del_creator_pending abi)
    (mutex_del_creator_publication_step creator) (mutex_del_creator_publication_effect creator)
    (mutex_del_creator_publication_extension_valid external platform port abi creator Hargs)
    sg KernelClientHeapClosed before KernelClientHeapClosed after frame Htrace state Hpre)
    as [returned [Hlogical Hafter]].
  exists returned, after; split; [exact Htrace|]. split; assumption.
Qed.

(** A running creator's pending cut and a carried creator own disjoint
    real ECB bytes. The address exclusion is derived here, not installed
    as an invented source guard or a client protocol premise. *)
Lemma mutex_del_creator_pending_separate_allocation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg pointer state observer allocation,
  mutex_del_creator_pending abi sg pointer state ** event_private_storage_rep sg observer allocation |--
    coq_prop (pointer <> event_pool_addr sg observer).
Proof.
  intros external platform port abi sg pointer state observer allocation.
  unfold mutex_del_creator_pending; Intros eid current.
  destruct (Z.eq_dec pointer (event_pool_addr sg observer)) as [Hequal|Hdifferent]; [|entailer!].
  assert (Hpointer : pointer = event_pool_addr sg eid) by tauto.
  assert (eid = observer) by (apply event_pool_addr_injective with (sg := sg); congruence); subst eid.
  unfold event_private_storage_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg observer) current.(eventPrivateStorage) EventPtrField
    ltac:(unfold event_fields; simpl; tauto)).
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg observer) allocation.(eventPrivateStorage) EventPtrField
    ltac:(unfold event_fields; simpl; tauto)).
  cbn [event_cell event_field_offset].
  destruct (current.(eventPrivateStorage) EventPtrField), (allocation.(eventPrivateStorage) EventPtrField).
  all: repeat match goal with
    | |- context [?p # Ptr |-> ?v] => sep_apply_l_atomic (store_ptr_undef_store_ptr p v)
    end.
  all: prop_apply (dup_undef_store_ptr (event_pool_addr sg observer + 4)); entailer!.
Qed.

Lemma mutex_del_creator_stores_keep_other_allocation : forall eid writes state result returned observer allocation,
  observer <> eid -> state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  event_create_private_stores eid writes state result returned ->
  returned.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation.
Proof.
  intros eid writes; induction writes as [|[field value] rest IH];
    intros state result returned observer allocation Hdifferent Hget Hstores.
  - destruct Hstores as [_ ->]; exact Hget.
  - destruct Hstores as [current [Hcurrent Htail]].
    eapply IH; [exact Hdifferent| |exact Htail].
    cbn [replace_EventS EventState event_private_write event_set_lifecycle eventLifecycle eventPrivate].
    rewrite kernel_map_set_other by exact Hdifferent; exact Hget.
Qed.

(** The actual extension preserves the separate creator even when another
    creator completes publication. Unlike the free-pop-only projection,
    this statement does not assert that EVERY old private lookup survives:
    the publishing client's own allocation is deliberately consumed. *)
Lemma mutex_del_creator_publication_step_keeps_carried : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut state before next after
  observer allocation (frame : Assertion),
  mutex_del_creator_arguments creator -> UCOS2_state_inv sg state ->
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  mutex_del_creator_publication_step creator sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_private_storage_rep sg observer allocation ** frame)) before ->
  exists returned,
    mutex_del_creator_publication_effect creator sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      (event_private_storage_rep sg observer allocation ** frame)) after.
Proof.
  intros external platform port abi creator sg cut state before next after observer allocation frame
    Hargs Hvalid Hget Hsource Hpre.
  destruct Hsource as [before cut after Hallocate|pointer before after Hwrites].
  - destruct (mutex_del_creator_allocate_pending external platform port abi sg state before cut after
      (event_private_storage_rep sg observer allocation ** frame) Hallocate Hpre)
      as [returned [Heffect Hafter]].
    exists returned; split; [constructor; exact Heffect|]. split; [|exact Hafter].
    destruct Heffect; eapply mutex_del_allocate_keeps_existing_private; eassumption.
  - assert (Hdifferent : pointer <> event_pool_addr sg observer).
    { assert (Hseparate : kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg
        (KernelClientHeapExtra pointer) state ** (event_private_storage_rep sg observer allocation ** frame) |--
        coq_prop (pointer <> event_pool_addr sg observer)).
      { cbn [kernel_client_heap_resources].
        prop_apply (mutex_del_creator_pending_separate_allocation external platform port abi sg pointer
          state observer allocation); entailer!. }
      exact (Hseparate before Hpre). }
    destruct (mutex_del_creator_initialization_publish external platform port abi sg creator pointer state before
      (event_private_storage_rep sg observer allocation ** frame) Hargs Hpre)
      as [eid [current [initialized [final [produced [Hpointer [Hcurrent [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    assert (Hdistinct : observer <> eid) by congruence.
    exists (mutex_del_creator_published_state creator initialized eid final).
    split; [econstructor; eassumption|]. split; [|exact Hafter].
    cbn [mutex_del_creator_published_state replace_EventS EventState event_publish eventLifecycle eventPrivate].
    rewrite kernel_map_set_other by exact Hdistinct.
    eapply mutex_del_creator_stores_keep_other_allocation; eassumption.
Qed.

Lemma mutex_del_creator_publication_cut_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg cut state,
  kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state |--
    coq_prop (UCOS2_state_inv sg state).
Proof.
  intros external platform port abi sg cut state; destruct cut; cbn [kernel_client_heap_resources].
  - unfold kernel_client_heap_world, kernel_program_inv; entailer!.
  - unfold kernel_client_heap_publication; entailer!.
  - unfold mutex_del_creator_pending; Intros eid allocation.
    unfold kernel_client_heap_world, kernel_program_inv; entailer!.
Qed.

Lemma mutex_del_creator_publication_registered_step : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut state before next after
  observer allocation (frame : Assertion),
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  kernel_client_heap_step (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_private_storage_rep sg observer allocation ** frame)) before ->
  exists returned,
    kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      (event_private_storage_rep sg observer allocation ** frame)) after.
Proof.
  intros external platform port abi creator sg cut state before next after observer allocation frame
    Hargs Hget Hsource Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Hpre as [owned [rest [_ [Howned _]]]].
    exact (mutex_del_creator_publication_cut_valid external platform port abi sg cut state owned Howned). }
  destruct Hsource as [before after Henter|before after Hexit|publication before after Hpublish|
    cut before next after Hregistered].
  - exists (os_int_enter_state state); split; [constructor|]. split; [exact Hget|].
    eapply kernel_client_int_enter_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state).
    split; [constructor|]. split; [exact Hget|]. eapply kernel_client_int_exit_resources; eassumption.
  - destruct (kernel_client_publication_resources external platform port abi sg publication state
      (event_private_storage_rep sg observer allocation ** frame) before after Hpre Hpublish)
      as [[Hinput Hstate] Hafter].
    exists (task_create_stack_publication_state sg publication state).
    split; [constructor; exact Hinput|]. split; [exact Hget|exact Hafter].
  - destruct (mutex_del_creator_publication_step_keeps_carried external platform port abi creator sg
      cut state before next after observer allocation frame Hargs Hvalid Hget Hregistered Hpre)
      as [returned [Heffect [Hlookup Hafter]]].
    exists returned; split; [constructor; exact Heffect|]. split; assumption.
Qed.

(** Any actual starting resource cut is allowed. In particular the
    Task-publication and creator-pending cases have not been changed into
    Closed-only counter paths. Every intermediate step uses the SAME heap
    as the supplied execution and retains the observer's physical ECB. *)
Lemma mutex_del_creator_publication_registered_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut before next after
  observer allocation (frame : Assertion),
  mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  forall state,
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_private_storage_rep sg observer allocation ** frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      (event_private_storage_rep sg observer allocation ** frame)) after.
Proof.
  intros external platform port abi creator sg cut before next after observer allocation frame Hargs Hsource.
  induction Hsource; intros state Hget Hpre.
  - exists state; split; [constructor|]. split; assumption.
  - destruct (mutex_del_creator_publication_registered_step external platform port abi creator sg
      cut state before middle_cut middle observer allocation frame Hargs Hget H Hpre)
      as [middle_state [Hstep [Hlookup Hmiddle]]].
    destruct (IHHsource middle_state Hlookup Hmiddle) as [returned [Htail [Hget_returned Hafter]]].
    exists returned; split; [econstructor; eassumption|]. split; assumption.
Qed.

(** The same Type byte is offered to the adopted private selected-Save
    consumer, after real registered clients including allocation AND
    publication. It is read from the carried image, never synthesized from
    a Closed invariant or obtained through a global lookup assumption. *)
Lemma mutex_del_creator_publication_trace_type : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg pointer cut state before after
  observer allocation observed (frame : Assertion),
  mutex_del_creator_arguments creator -> pointer = event_pool_addr sg observer ->
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some observed ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before KernelClientHeapClosed after ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_private_storage_rep sg observer allocation ** frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg
      cut state KernelClientHeapClosed returned /\
    (pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer returned observed ** frame) after.
Proof.
  intros external platform port abi creator sg pointer cut state before after observer allocation observed frame
    Hargs Hpointer Hget Htype Hsource Hpre.
  destruct (mutex_del_creator_publication_registered_trace external platform port abi creator sg cut before
    KernelClientHeapClosed after observer allocation frame Hargs Hsource state Hget Hpre)
    as [returned [Hlogical [Hlookup Hafter]]].
  exists returned; split; [exact Hlogical|].
  assert (Hloan : kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg
      KernelClientHeapClosed returned ** (event_private_storage_rep sg observer allocation ** frame) |--
    pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer returned observed ** frame).
  { cbn [kernel_client_heap_resources].
    sep_apply_l_atomic (event_private_storage_rep_split_type sg observer allocation observed Htype).
    unfold mutex_del_creator_type_residual; Exists observer allocation; rewrite Hpointer; entailer!. }
  exact (Hloan after Hafter).
Qed.
