Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.

Import UCOS2_C_Rules ListNotations EventStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Definition sem_create_link_addr (base : addr) : addr :=
  &((base) # "os_event" ->ₛ "OSEventPtr").

(** The selected names-disabled C/ABI binding, not an axiom about QCP's
    abstract address interpreter.  The pointer used by the source is the
    current pool head after Save; no entry-snapshot head is assumed here.
    The remaining field bindings are supplied at their actual source uses. *)
Definition sem_create_source_binding (sg : StableGlobVars) : Prop :=
  &("OSIntNesting") = sg.(g_OSIntNesting) /\
  &("OSEventFreeList") = sg.(g_OSEventFreeList) /\
  sizeof_alias_type "os_event" = 20 /\
  forall eid, 0 <= eid < sg.(osMaxEvents) ->
    0 < event_pool_addr sg eid <= 4294967295 /\
    sem_create_link_addr (event_pool_addr sg eid) =
      event_pool_addr sg eid + 4.

Definition sem_create_pool_head (sg : StableGlobVars) (state : UCOS2_Verify_State) : addr :=
  event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)).

Definition sem_create_pool_frame (sg : StableGlobVars) (state : UCOS2_Verify_State) : Assertion :=
  store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
  event_free_storage_rep sg state.(EventState) **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Definition sem_create_node_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (image : EventStorage) : Assertion :=
  event_storage_without_field false (event_pool_addr sg eid) image EventPtrField **
  event_free_storage_without_eid sg state.(EventState) eid **
  store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Lemma sem_create_pool_split_head : forall sg state,
  sem_create_source_binding sg ->
  UCOS2_inv sg state --||--
    coq_prop (UCOS2_state_inv sg state) &&
    (&("OSEventFreeList") # Ptr |-> sem_create_pool_head sg state **
     sem_create_pool_frame sg state).
Proof.
  intros sg state [_ [Hroot _]].
  rewrite UCOS2_inv_split_event_queue.
  unfold event_raw_rep, event_free_root_rep, sem_create_pool_head, sem_create_pool_frame.
  rewrite Hroot; split; entailer!.
Qed.

Lemma sem_create_pool_nonempty_facts : forall sg state eid rest,
  UCOS2_state_inv sg state -> state.(EventState).(unUsedEventStates) = eid :: rest ->
  0 <= eid < sg.(osMaxEvents) /\ exists image,
    state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
    image EventPtrField = Some (event_encode_pool_link sg (hd_error rest)).
Proof.
  intros sg state eid rest Hvalid Hhead.
  pose proof Hvalid as [_ [_ [_ [[[[Hnd [Hrange Hpartition]] Hdisjoint]
    [[Hdomain [Hlinks Htypes]] Hremaining]] Hother]]]].
  split; [apply Hrange; rewrite Hhead; simpl; auto|].
  destruct (proj2 (Hdomain eid) ltac:(rewrite Hhead; simpl; auto)) as [image Himage].
  exists image; split; [exact Himage|].
  specialize (Hlinks eid image Himage); rewrite Hhead in Hlinks.
  simpl in Hlinks; destruct (Z.eq_dec eid eid); [exact Hlinks|contradiction].
Qed.

(** Both C branches are justified: NULL means exhaustion, and a nonempty
    pool supplies a non-NULL address and the actual next link. *)
Lemma sem_create_pool_head_null_iff : forall sg state,
  sem_create_source_binding sg -> UCOS2_state_inv sg state ->
  sem_create_pool_head sg state = 0 <-> state.(EventState).(unUsedEventStates) = [].
Proof.
  intros sg state [_ [_ [_ Hlayout]]] Hvalid.
  unfold sem_create_pool_head.
  destruct state.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - simpl; tauto.
  - destruct (sem_create_pool_nonempty_facts sg state eid rest Hvalid Hhead) as [Hrange _].
    destruct (Hlayout eid Hrange) as [[Hpositive Hupper] Hptr].
    simpl; split; [lia|discriminate].
Qed.

Lemma sem_create_pool_split_node : forall sg state eid rest image,
  sem_create_source_binding sg -> UCOS2_state_inv sg state ->
  state.(EventState).(unUsedEventStates) = eid :: rest ->
  state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  sem_create_pool_frame sg state |--
    sem_create_link_addr (event_pool_addr sg eid) # Ptr |->
      event_encode_pool_link sg (hd_error rest) ** sem_create_node_frame sg state eid image.
Proof.
  intros sg state eid rest image [_ [_ [_ Hlayout]]] Hvalid Hhead Himage.
  destruct (sem_create_pool_nonempty_facts sg state eid rest Hvalid Hhead)
    as [Hrange [actual [Hactual Hnext]]].
  assert (actual = image) by congruence; subst actual.
  destruct (Hlayout eid Hrange) as [Haddress Hptr].
  unfold sem_create_pool_frame, sem_create_node_frame.
  sep_apply_l_atomic (event_free_storage_split_eid sg state.(EventState) eid image Himage).
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  rewrite Hnames.
  sep_apply_l_atomic (event_storage_split_field false (event_pool_addr sg eid) image
    EventPtrField ltac:(unfold event_fields; simpl; tauto)).
  unfold event_cell, event_field_offset; rewrite Hnext, Hptr; entailer!.
Qed.

(** The root cell on the left has already been changed by the C store.
    The node's next field itself is still unchanged.  No field or padding
    byte is discarded when the complete ECB becomes private. *)
Lemma sem_create_pool_merge_detached_node : forall sg state eid rest image,
  sem_create_source_binding sg -> UCOS2_state_inv sg state ->
  state.(EventState).(unUsedEventStates) = eid :: rest ->
  state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  &("OSEventFreeList") # Ptr |-> event_encode_pool_link sg (hd_error rest) **
    (sem_create_link_addr (event_pool_addr sg eid) # Ptr |->
       event_encode_pool_link sg (hd_error rest) ** sem_create_node_frame sg state eid image) |--
  event_storage_rep false (event_pool_addr sg eid) image **
    UCOS2_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state).
Proof.
  intros sg state eid rest image [_ [Hroot [_ Hlayout]]] Hvalid Hhead Himage.
  destruct (sem_create_pool_nonempty_facts sg state eid rest Hvalid Hhead)
    as [Hrange [actual [Hactual Hnext]]].
  assert (actual = image) by congruence; subst actual.
  destruct (Hlayout eid Hrange) as [Haddress Hptr].
  unfold sem_create_node_frame; rewrite Hroot, Hptr.
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hcell : (event_pool_addr sg eid + 4) # Ptr |->
      event_encode_pool_link sg (hd_error rest) =
    event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField)).
  { unfold event_cell, event_field_offset; rewrite Hnext; reflexivity. }
  rewrite Hcell.
  assert (Hrestore :
    (event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField) **
     event_storage_without_field false (event_pool_addr sg eid) image EventPtrField) **
     event_free_storage_without_eid sg state.(EventState) eid |--
     event_free_storage_rep sg state.(EventState)).
  { sep_apply_l_atomic (event_storage_merge_field false (event_pool_addr sg eid) image
      EventPtrField ltac:(unfold event_fields; simpl; tauto)).
    rewrite <- Hnames; apply event_free_storage_merge_eid; exact Himage. }
  eapply derivable1_trans with (y :=
    ((event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField) **
      event_storage_without_field false (event_pool_addr sg eid) image EventPtrField) **
      event_free_storage_without_eid sg state.(EventState) eid) **
    (store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
     sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state)).
  - entailer!.
  - sep_apply_l_atomic Hrestore.
    pose proof (UCOS2_inv_merge_event_detach_head sg state eid rest image Hvalid Hhead Himage) as Hmerge.
    rewrite Hnames in Hmerge.
    eapply derivable1_trans; [|exact Hmerge]; entailer!.
Qed.

Definition sem_create_head_facts (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (rest : list EventID) (image : EventStorage) : Prop :=
  state.(EventState).(unUsedEventStates) = eid :: rest /\
  state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image.

(** This is the precise restore-side heap.  Allocation metadata records
    ownership history, while the separate assertion owns the real ECB.
    It does not open the unmasked shared invariant or perform publication. *)
Definition sem_create_allocation_post (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pointer : addr) : Assertion :=
  EX allocated result,
    coq_prop (event_create_allocate_critical entry result allocated /\
      pointer = event_create_return_ptr sg result) &&
    ((match result with
      | None => emp
      | Some (eid, image) => event_storage_rep false (event_pool_addr sg eid) image
      end) ** UCOS2_inv sg allocated).

Lemma sem_create_allocation_empty : forall sg entry,
  entry.(EventState).(unUsedEventStates) = [] ->
  UCOS2_inv sg entry |-- sem_create_allocation_post sg entry 0.
Proof.
  intros sg entry Hempty; unfold sem_create_allocation_post.
  Exists entry (@None (EventID * EventStorage)); simpl.
  assert (Hstep : event_create_allocate_critical entry None entry).
  { unfold event_create_allocate_critical; rewrite Hempty; split; reflexivity. }
  entailer!.
Qed.

Lemma sem_create_allocation_nonempty : forall sg entry eid rest image,
  entry.(EventState).(unUsedEventStates) = eid :: rest ->
  entry.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  event_storage_rep false (event_pool_addr sg eid) image **
    UCOS2_inv sg (replace_EventS (event_detach_head entry.(EventState) eid rest image) entry) |--
  sem_create_allocation_post sg entry (event_pool_addr sg eid).
Proof.
  intros sg entry eid rest image Hhead Himage; unfold sem_create_allocation_post.
  Exists (replace_EventS (event_detach_head entry.(EventState) eid rest image) entry)
    (Some (eid, image)); simpl.
  assert (Hstep : event_create_allocate_critical entry (Some (eid, image))
    (replace_EventS (event_detach_head entry.(EventState) eid rest image) entry)).
  { unfold event_create_allocate_critical; rewrite Hhead.
    exists image; repeat split; assumption || reflexivity. }
  entailer!.
Qed.

(** The three caller stores and the nine bytes owned by WaitListInit are
    distinct from the four padding bytes.  These assertions own only the
    detached ECB: neither a shared invariant nor an environment transition
    is smuggled into the helper's contract. *)
Definition sem_create_initialization_frame (base : addr) (image : EventStorage) : Assertion :=
  event_cell base EventPadding1 (image EventPadding1) **
  event_cell base EventPadding2 (image EventPadding2) **
  event_cell base EventPadding3 (image EventPadding3) **
  event_cell base EventPadding19 (image EventPadding19).

Definition sem_create_initialization_pre (base : addr) (image : EventStorage) : Assertion :=
  base # UChar |->_ ** (base + 8) # UShort |->_ ** (base + 4) # Ptr |->_ **
  event_wait_list_init_pre (base + 10) (base + 11) **
  sem_create_initialization_frame base image.

Definition sem_create_initialization_post (base : addr) (image : EventStorage)
  (count : Z) : Assertion :=
  base # UChar |-> 3 ** (base + 8) # UShort |-> count ** (base + 4) # Ptr |-> 0 **
  event_wait_list_init_post (base + 10) (base + 11) **
  sem_create_initialization_frame base image.

Lemma sem_create_initialization_split : forall base image,
  event_storage_rep false base image |-- sem_create_initialization_pre base image.
Proof.
  intros base image; eapply derivable1_trans;
    [apply event_wait_list_init_storage_split|].
  unfold sem_create_initialization_pre, sem_create_initialization_frame,
    event_wait_list_init_storage_frame.
  assert (Htype : event_cell base EventTypeField (image EventTypeField) |-- base # UChar |->_).
  { unfold event_cell, event_field_offset; replace (base + 0) with base by lia.
    destruct (image EventTypeField); [apply store_uchar_undef_store_uchar|entailer!]. }
  assert (Hcount : event_cell base EventCntField (image EventCntField) |-- (base + 8) # UShort |->_).
  { unfold event_cell, event_field_offset; destruct (image EventCntField);
      [apply store_ushort_undef_store_ushort|entailer!]. }
  assert (Hpointer : event_cell base EventPtrField (image EventPtrField) |-- (base + 4) # Ptr |->_).
  { unfold event_cell, event_field_offset; destruct (image EventPtrField);
      [apply store_ptr_undef_store_ptr|entailer!]. }
  sep_apply_l_atomic Htype; sep_apply_l_atomic Hcount; sep_apply_l_atomic Hpointer; entailer!.
Qed.

Lemma sem_create_initialization_merge : forall base image count,
  sem_create_initialization_post base image count |--
  event_storage_rep false base (event_create_image false 3 count 0 0 image).
Proof.
  intros base image count.
  set (payload := event_write (event_write (event_write image EventTypeField (Some 3))
    EventCntField (Some count)) EventPtrField (Some 0)).
  assert (Himage : event_wait_list_init_image payload = event_create_image false 3 count 0 0 image)
    by reflexivity.
  assert (Hfields : forall field, payload field =
    match field with
    | EventTypeField => Some 3
    | EventCntField => Some count
    | EventPtrField => Some 0
    | _ => image field
    end).
  { intro field; destruct field; reflexivity. }
  rewrite <- Himage.
  eapply derivable1_trans; [|apply event_wait_list_init_storage_merge].
  unfold sem_create_initialization_post, sem_create_initialization_frame,
    event_wait_list_init_storage_frame.
  rewrite !Hfields.
  unfold event_cell, event_field_offset.
  replace (base + 0) with base by lia; entailer!.
Qed.

Definition sem_create_allocation_facts (sg : StableGlobVars) (entry allocated : UCOS2_Verify_State)
  (eid : EventID) (image : EventStorage) : Prop :=
  UCOS2_state_inv sg entry /\ event_create_allocate_critical entry (Some (eid, image)) allocated.

Lemma sem_create_allocation_facts_private : forall sg entry allocated eid image,
  sem_create_allocation_facts sg entry allocated eid image ->
  UCOS2_state_inv sg allocated /\
  allocated.(EventState).(eventLifecycle).(eventPrivate) eid =
    Some (sem_create_allocation_identity entry image).
Proof.
  intros sg entry allocated eid image [Hvalid Hallocate]; split.
  - eapply event_create_allocate_critical_preserves_validity; eassumption.
  - exact (proj2 (event_create_allocate_critical_private_result entry eid image allocated Hallocate)).
Qed.

Lemma sem_create_allocated_id_valid : forall sg entry allocated eid image,
  sem_create_allocation_facts sg entry allocated eid image -> valid_event_id sg eid.
Proof.
  intros sg entry allocated eid image Hfacts.
  destruct (sem_create_allocation_facts_private _ _ _ _ _ Hfacts) as [Hvalid Hget].
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  exact (proj1 (event_pool_private_not_free sg allocated.(EventState) eid _ Hpool Hget)).
Qed.

Definition sem_create_initialization_prefix (count phase : Z) : list (EventField * Z) :=
  if Z.eqb phase 0 then [] else
  if Z.eqb phase 1 then [(EventTypeField, 3)] else
  if Z.eqb phase 2 then [(EventTypeField, 3); (EventCntField, count)] else
  if Z.eqb phase 3 then [(EventTypeField, 3); (EventCntField, count); (EventPtrField, 0)] else
  event_create_initialization_fields false 3 count 0 0.

Definition sem_create_initialization_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask count : Z) (entry allocated : UCOS2_Verify_State)
  (eid : EventID) (image : EventStorage) (phase : Z) : Assertion :=
  coq_prop (sem_create_allocation_facts sg entry allocated eid image) &&
  sem_create_private_context platform critical sg invocation origin mask eid allocated
    (sem_create_allocation_identity entry image) (sem_create_initialization_prefix count phase).

Lemma sem_create_initialization_context_begin :
  forall platform critical sg invocation origin mask count entry allocated eid image,
  sem_create_allocation_facts sg entry allocated eid image ->
  sem_create_pre platform sg invocation origin mask allocated |--
  sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 0.
Proof.
  intros; unfold sem_create_initialization_context, sem_create_initialization_prefix.
  sep_apply_l_atomic (sem_create_private_context_begin platform critical sg invocation origin mask
    eid allocated (sem_create_allocation_identity entry image)); entailer!.
Qed.

Lemma sem_create_initialization_context_merge_type :
  forall platform critical sg invocation origin mask count entry allocated eid image,
  event_pool_addr sg eid # UChar |-> 3 **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 0 |--
  event_pool_addr sg eid # UChar |-> 3 **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 1.
Proof.
  intros; unfold sem_create_initialization_context; Intros.
  match goal with H : sem_create_allocation_facts _ _ _ _ _ |- _ =>
    destruct (sem_create_allocation_facts_private _ _ _ _ _ H) as [Hvalid Hget] end.
  pose proof (sem_create_private_context_merge_field platform critical sg invocation origin mask eid allocated
    (sem_create_allocation_identity entry image) [] EventTypeField 3 Hvalid Hget) as Hmerge.
  cbn [event_cell event_field_offset] in Hmerge.
  replace (event_pool_addr sg eid + 0) with (event_pool_addr sg eid) in Hmerge by lia.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma sem_create_initialization_context_merge_count :
  forall platform critical sg invocation origin mask count entry allocated eid image,
  (event_pool_addr sg eid + 8) # UShort |-> count **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 1 |--
  (event_pool_addr sg eid + 8) # UShort |-> count **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 2.
Proof.
  intros; unfold sem_create_initialization_context; Intros.
  match goal with H : sem_create_allocation_facts _ _ _ _ _ |- _ =>
    destruct (sem_create_allocation_facts_private _ _ _ _ _ H) as [Hvalid Hget] end.
  sep_apply_l_atomic (sem_create_private_context_merge_field platform critical sg invocation origin mask eid allocated
    (sem_create_allocation_identity entry image) [(EventTypeField, 3)] EventCntField count Hvalid Hget); entailer!.
Qed.

Lemma sem_create_initialization_context_merge_pointer :
  forall platform critical sg invocation origin mask count entry allocated eid image,
  (event_pool_addr sg eid + 4) # Ptr |-> 0 **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 2 |--
  (event_pool_addr sg eid + 4) # Ptr |-> 0 **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 3.
Proof.
  intros; unfold sem_create_initialization_context; Intros.
  match goal with H : sem_create_allocation_facts _ _ _ _ _ |- _ =>
    destruct (sem_create_allocation_facts_private _ _ _ _ _ H) as [Hvalid Hget] end.
  sep_apply_l_atomic (sem_create_private_context_merge_field platform critical sg invocation origin mask eid allocated
    (sem_create_allocation_identity entry image) [(EventTypeField, 3); (EventCntField, count)] EventPtrField 0 Hvalid Hget); entailer!.
Qed.

Lemma sem_create_initialization_context_merge_wait_list :
  forall platform critical sg invocation origin mask count entry allocated eid image,
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 3 |--
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 4.
Proof.
  intros; unfold sem_create_initialization_context; Intros.
  match goal with H : sem_create_allocation_facts _ _ _ _ _ |- _ =>
    destruct (sem_create_allocation_facts_private _ _ _ _ _ H) as [Hvalid Hget] end.
  sep_apply_l_atomic (sem_create_private_context_merge_wait_list platform critical sg invocation origin mask eid allocated
    (sem_create_allocation_identity entry image) (sem_create_initialization_prefix count 3) Hvalid Hget); entailer!.
Qed.

Lemma sem_create_initialization_context_publish :
  forall platform critical sg invocation origin mask count before entry allocated eid image,
  critical_region_interval critical sg invocation before entry -> sem_create_int_nesting before <= 0 ->
  0 <= count <= 65535 ->
  event_storage_rep false (event_pool_addr sg eid) (event_create_image false 3 count 0 0 image) **
    sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 4 |--
  EX after, coq_prop (sem_create_call_relation critical sg invocation count before (event_pool_addr sg eid) after) &&
    sem_create_pre platform sg invocation origin mask after.
Proof.
  intros platform critical sg invocation origin mask count before entry allocated eid image Hentry Hnesting Hcount.
  unfold sem_create_initialization_context; Intros.
  match goal with H : sem_create_allocation_facts _ _ _ _ _ |- _ => destruct H as [Hvalid Hallocate] end.
  eapply sem_create_private_context_publish; eassumption.
Qed.

(** Restore closes the current allocation checkpoint and keeps its exact
    private bytes. It does not initialize any payload or promise a future
    valid/published event. The common CPU/CSL boundary remains conditional. *)
Definition sem_create_restored (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (entry : UCOS2_Verify_State) (pointer : addr) : Assertion :=
  EX allocated result,
    coq_prop (event_create_allocate_critical entry result allocated /\ pointer = event_create_return_ptr sg result) &&
    ((match result with
      | None => emp
      | Some (eid, image) => event_storage_rep false (event_pool_addr sg eid) image
      end) ** sem_create_pre platform sg invocation origin mask allocated).

Lemma sem_create_restore_consequence : forall platform (critical : CriticalRegionResources) sg invocation origin mask entry pointer,
  interrupt_platform_running platform invocation origin mask ** sem_create_allocation_post sg entry pointer |--
  sem_create_restored platform sg invocation origin mask entry pointer.
Proof.
  intros; unfold sem_create_allocation_post, sem_create_restored; Intros allocated result.
  Exists allocated result.
  rewrite (sem_create_pre_running_inv_equiv platform critical sg invocation origin mask allocated); entailer!.
Qed.

Lemma sem_create_restored_nonnull :
  forall platform critical sg invocation origin mask count entry pointer,
  UCOS2_state_inv sg entry -> event_table_layout_prop sg -> pointer <> 0 ->
  sem_create_restored platform sg invocation origin mask entry pointer |--
  EX eid image allocated,
    coq_prop (sem_create_allocation_facts sg entry allocated eid image /\
      event_object_layout_prop sg eid /\ pointer = event_pool_addr sg eid) &&
    (sem_create_initialization_pre (event_pool_addr sg eid) image **
     sem_create_initialization_context platform critical sg invocation origin mask count entry allocated eid image 0).
Proof.
  intros platform critical sg invocation origin mask count entry pointer Hvalid Htable Hnonnull.
  unfold sem_create_restored; Intros allocated result.
  match goal with H : _ /\ _ |- _ => destruct H as [Hallocate Hpointer] end.
  destruct result as [[eid image]|]; [|simpl in Hpointer; contradiction].
  assert (Hfacts : sem_create_allocation_facts sg entry allocated eid image) by (split; assumption).
  pose proof (event_table_layout_select sg eid Htable (sem_create_allocated_id_valid _ _ _ _ _ Hfacts)) as Hlayout.
  Exists eid image allocated.
  sep_apply_l_atomic (sem_create_initialization_split (event_pool_addr sg eid) image).
  sep_apply_l_atomic (sem_create_initialization_context_begin platform critical sg invocation origin mask
    count entry allocated eid image Hfacts); entailer!.
Qed.

Lemma sem_create_restored_null :
  forall platform critical sg invocation origin mask count before entry,
  sem_create_source_binding sg -> UCOS2_state_inv sg entry ->
  critical_region_interval critical sg invocation before entry -> sem_create_int_nesting before <= 0 ->
  sem_create_restored platform sg invocation origin mask entry 0 |--
  EX after, coq_prop (sem_create_call_relation critical sg invocation count before 0 after) &&
    sem_create_pre platform sg invocation origin mask after.
Proof.
  intros platform critical sg invocation origin mask count before entry Hsource Hvalid Hentry Hnesting.
  unfold sem_create_restored; Intros allocated result.
  match goal with H : _ /\ _ |- _ => destruct H as [Hallocate Hpointer] end.
  destruct result as [[eid image]|].
  - assert (Hfacts : sem_create_allocation_facts sg entry allocated eid image) by (split; assumption).
    pose proof (sem_create_allocated_id_valid _ _ _ _ _ Hfacts) as Hid.
    destruct Hsource as [_ [_ [_ Hlayout]]]; destruct (Hlayout eid Hid) as [[Hpositive _] _].
    cbn [event_create_return_ptr] in Hpointer; exfalso; lia.
  - assert (Hcall : sem_create_call_relation critical sg invocation count before 0 allocated).
    { unfold sem_create_call_relation.
      assert (Hnotisr : event_create_isr_rejected (sem_create_int_nesting before) = false)
        by (apply Z.ltb_ge; exact Hnesting).
      rewrite Hnotisr; exists entry, allocated, None.
      split; [exact Hentry|]. split; [exact Hallocate|]. split; [reflexivity|constructor]. }
    Exists allocated; entailer!.
Qed.
