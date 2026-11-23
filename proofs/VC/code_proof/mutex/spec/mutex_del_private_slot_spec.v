Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A real creator-owned ECB is neither a published event nor a free node.
    This residual lends ONLY its actual type byte, retaining every other
    private byte. The source/IRQ caller must supply this ownership; the
    global program invariant and an allocation identifier cannot do so. *)
Definition event_private_storage_without_type sg eid allocation : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) allocation.(eventPrivateStorage) EventTypeField.

Lemma event_private_storage_rep_split_type : forall sg eid allocation observed,
  allocation.(eventPrivateStorage) EventTypeField = Some observed ->
  event_private_storage_rep sg eid allocation |--
    (event_pool_addr sg eid) # UChar |-> observed **
    event_private_storage_without_type sg eid allocation.
Proof.
  intros sg eid allocation observed Htype.
  unfold event_private_storage_rep, event_private_storage_without_type.
  pose proof (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) allocation.(eventPrivateStorage) EventTypeField
    ltac:(unfold event_fields; simpl; auto)) as Hsplit.
  rewrite Htype in Hsplit.
  cbn [event_cell event_field_offset] in Hsplit.
  rewrite Z.add_0_r in Hsplit; exact Hsplit.
Qed.

Lemma event_private_storage_rep_merge_type : forall sg eid allocation observed,
  allocation.(eventPrivateStorage) EventTypeField = Some observed ->
  (event_pool_addr sg eid) # UChar |-> observed **
    event_private_storage_without_type sg eid allocation |--
  event_private_storage_rep sg eid allocation.
Proof.
  intros sg eid allocation observed Htype.
  unfold event_private_storage_rep, event_private_storage_without_type.
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) allocation.(eventPrivateStorage) EventTypeField
    ltac:(unfold event_fields; simpl; auto)) as Hmerge.
  rewrite Htype in Hmerge.
  cbn [event_cell event_field_offset] in Hmerge.
  rewrite Z.add_0_r in Hmerge; exact Hmerge.
Qed.

Lemma event_private_storage_type_load : forall sg eid allocation observed heap (frame : Assertion),
  allocation.(eventPrivateStorage) EventTypeField = Some observed ->
  (event_private_storage_rep sg eid allocation ** frame) heap ->
  uchar_load (event_pool_addr sg eid) observed heap.
Proof.
  intros sg eid allocation observed heap frame Htype Hpre.
  assert (Hopen : event_private_storage_rep sg eid allocation ** frame |--
    (event_pool_addr sg eid) # UChar |-> observed **
    (event_private_storage_without_type sg eid allocation ** frame)).
  { sep_apply_l_atomic (event_private_storage_rep_split_type sg eid allocation observed Htype); entailer!. }
  exact (framed_uchar_store_load _ _ _ _ (Hopen heap Hpre)).
Qed.

(** Allocation itself preserves global validity, while removing the free
    slot from the public query domain. Thus validity cannot imply that
    every statically allocated ECB remains used-or-free at a later Save. *)
Lemma event_create_allocate_not_public_slot : forall sg before eid image after,
  UCOS2_state_inv sg before ->
  event_create_allocate_critical before (Some (eid, image)) after ->
  forall observed, ~ sem_query_public_slot after eid observed.
Proof.
  intros sg before eid image after Hvalid Hrun observed.
  pose proof (event_create_allocate_critical_preserves_validity sg before _ after Hvalid Hrun)
    as Hafter.
  destruct (event_create_allocate_critical_private_result before eid image after Hrun)
    as [_ Hprivate].
  pose proof Hafter as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_private_not_free sg after.(EventState) eid _ Hpool Hprivate)
    as [_ [Hnot Hnone]].
  intros [Hused|[_ Hfree]]; [unfold mutex_query_lookup in Hused; congruence|contradiction].
Qed.

(** At the first real creator Restore, the untouched Type byte is UNUSED.
    This pure source fact still does not produce the private byte resource. *)
Lemma event_create_allocate_private_type_unused : forall sg before eid image after,
  UCOS2_state_inv sg before ->
  event_create_allocate_critical before (Some (eid, image)) after ->
  exists allocation,
    after.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    allocation.(eventPrivateStorage) EventTypeField = Some 0.
Proof.
  intros sg before eid image after Hvalid Hrun.
  destruct (event_create_allocate_critical_private_result before eid image after Hrun)
    as [_ Hprivate].
  eexists; split; [exact Hprivate|].
  eapply event_create_allocate_critical_image_type; eassumption.
Qed.

(** A source store prefix can change Type only to the actual primitive's
    non-Mutex tag. This is not a restriction on arbitrary generic stores;
    the following source-list lemma supplies the condition for the real
    Sem/Mbox/Queue initialization sequences. *)
Lemma event_create_stores_image_type_non_mutex : forall writes image observed,
  image EventTypeField = Some observed -> observed <> 4 ->
  Forall (fun write => fst write = EventTypeField -> snd write <> 4) writes ->
  exists current, event_create_stores_image image writes EventTypeField = Some current /\ current <> 4.
Proof.
  intros writes; induction writes as [|[field value] rest IH]; intros image observed Htype Hnot Hwrites.
  - exists observed; split; assumption.
  - inversion Hwrites as [|write tail Hhead Htail]; subst.
    cbn [event_create_stores_image fold_left fst snd].
    change (exists current,
      event_create_stores_image (event_write image field (Some value)) rest EventTypeField = Some current /\
      current <> 4).
    destruct (EventField_eq_dec EventTypeField field) as [Heq|Hdifferent].
    + subst field; eapply IH with (observed := value).
      * unfold event_write; apply field_update_same.
      * apply Hhead; reflexivity.
      * exact Htail.
    + eapply IH with (observed := observed); [|exact Hnot|exact Htail].
      unfold event_write; rewrite field_update_other by exact Hdifferent; exact Htype.
Qed.

Lemma event_create_initialization_fields_non_mutex : forall named kind count pointer name,
  kind <> 4 ->
  Forall (fun write => fst write = EventTypeField -> snd write <> 4)
    (event_create_initialization_fields named kind count pointer name).
Proof.
  intros [] kind count pointer name Hkind;
    cbn [event_create_initialization_fields event_table_field];
    repeat constructor; simpl; intros; congruence.
Qed.

(** Every actual store prefix, including an empty prefix at Restore,
    retains a non-Mutex Type observation. The physical byte ownership is
    intentionally not inferred from this pure lifecycle theorem. *)
Lemma event_create_initialization_prefix_type_non_mutex : forall eid named kind count pointer name
  prefix remaining before result after allocation observed,
  kind <> 4 ->
  event_create_initialization_fields named kind count pointer name = prefix ++ remaining ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some observed -> observed <> 4 ->
  event_create_private_stores eid prefix before result after ->
  exists final current,
    after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateStorage) EventTypeField = Some current /\ current <> 4.
Proof.
  intros eid named kind count pointer name prefix remaining before result after allocation observed
    Hkind Hprefix Hget Htype Hnot Hrun.
  pose proof (event_create_initialization_fields_non_mutex named kind count pointer name Hkind) as Hall.
  rewrite Hprefix in Hall; apply Forall_app in Hall; destruct Hall as [Hprefix_fields _].
  destruct (event_create_private_stores_post_allocation eid prefix before result after allocation Hget Hrun)
    as [final [Hfinal [_ [_ [_ Himage]]]]].
  destruct (event_create_stores_image_type_non_mutex prefix allocation.(eventPrivateStorage) observed
    Htype Hnot Hprefix_fields) as [current [Hcurrent Hneq]].
  exists final, current; split; [exact Hfinal|].
  split; [rewrite Himage; exact Hcurrent|exact Hneq].
Qed.

(** Del's protected read consumes the actually lent private image and
    gives it back at the SAME heap/cut before Restore. This proves the
    type-error selector, not the later perr store: Restore is between the
    two C statements, and an old private image cannot be framed through
    that call without its actual source/resource producer. *)
Lemma mutex_del_private_type_guard_resources : forall sg state eid allocation observed heap
  (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some observed -> observed <> 4 ->
  (kernel_program_inv sg state ** event_private_storage_rep sg eid allocation ** frame) heap ->
  uchar_load (event_pool_addr sg eid) observed heap /\ observed <> 4 /\
  (kernel_program_inv sg state ** event_private_storage_rep sg eid allocation ** frame) heap.
Proof.
  intros sg state eid allocation observed heap frame Hget Htype Hnot Hpre.
  split; [|split; assumption].
  assert (Hread : kernel_program_inv sg state ** event_private_storage_rep sg eid allocation ** frame |--
    event_private_storage_rep sg eid allocation ** (kernel_program_inv sg state ** frame)) by entailer!.
  eapply event_private_storage_type_load; [exact Htype|exact (Hread heap Hpre)].
Qed.
