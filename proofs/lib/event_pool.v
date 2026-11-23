Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms Feq ListLib VMap.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.field_storage.
Import UCOS2_C_Rules ListNotations.
Module EventFieldStorage := FieldStorage Arch32 LittleEndian
  UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules.
Import EventFieldStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The shared ECB pool owns storage and allocation identity, not the
    interpretation of a Mutex/Sem/Mbox/Queue payload.  In particular a
    privately initializing ECB is not a published UNUSED event. *)
Definition event_fields (named : bool) : list EventField :=
  [EventTypeField; EventPadding1; EventPadding2; EventPadding3;
   EventPtrField; EventCntField; EventGrpField;
   EventTbl0; EventTbl1; EventTbl2; EventTbl3;
   EventTbl4; EventTbl5; EventTbl6; EventTbl7; EventPadding19] ++
  if named then [EventNameField] else [].

Definition event_field_offset (f : EventField) : Z :=
  match f with
  | EventTypeField => 0 | EventPtrField => 4 | EventCntField => 8 | EventGrpField => 10
  | EventTbl0 => 11 | EventTbl1 => 12 | EventTbl2 => 13 | EventTbl3 => 14
  | EventTbl4 => 15 | EventTbl5 => 16 | EventTbl6 => 17 | EventTbl7 => 18
  | EventPadding1 => 1 | EventPadding2 => 2 | EventPadding3 => 3
  | EventPadding19 => 19 | EventNameField => 20
  end.

Definition event_field_width (f : EventField) : nat :=
  match f with EventPtrField | EventNameField => 4 | EventCntField => 2 | _ => 1 end.

Lemma event_fields_nodup : forall named, NoDup (event_fields named).
Proof. intros []; unfold event_fields; repeat constructor; simpl; intuition discriminate. Qed.

Lemma event_layout_covers_bytes : forall named,
  flat_map (fun f => map (fun n => event_field_offset f + Z.of_nat n)
    (seq 0 (event_field_width f))) (event_fields named) =
  map Z.of_nat (seq 0 (if named then 24 else 20)).
Proof. intros []; reflexivity. Qed.

Lemma event_name_field_in_fields : forall named,
  In EventNameField (event_fields named) <-> named = true.
Proof. intros []; simpl; intuition discriminate. Qed.

(** These are numeric-profile cells. The theorem above checks their byte
    partition, not equality with QCP's symbolic C field-address operator.
    Each pool representation uses the same cfgEventNames as its address
    encoder: 20 bytes without names and 24 bytes with names. *)
Definition event_cell (base : addr) (f : EventField)
  (value : option Z) : Assertion :=
  let p := base + event_field_offset f in
  match f with
  | EventPtrField | EventNameField =>
      match value with Some v => p # Ptr |-> v | None => p # Ptr |->_ end
  | EventCntField =>
      match value with Some v => p # UShort |-> v | None => p # UShort |->_ end
  | _ => match value with Some v => p # UChar |-> v | None => p # UChar |->_ end
  end.

Definition event_write :=
  @field_update EventField (option Z) EventField_eq_dec.

Definition event_storage_rep (named : bool) (base : addr)
  (image : EventStorage) : Assertion :=
  store_fields EventField_eq_dec (event_cell base) (event_fields named) image.

Definition event_storage_without_field (named : bool) (base : addr)
  (image : EventStorage) (f : EventField) : Assertion :=
  store_fields EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec f (event_fields named)) image.

Lemma event_storage_rep_ext : forall named base before after,
  (forall field, In field (event_fields named) -> before field = after field) ->
  event_storage_rep named base before = event_storage_rep named base after.
Proof.
  intros named base before after Heq; unfold event_storage_rep, store_fields;
    f_equal; apply functional_extensionality; intro field; unfold fields_map.
  destruct (in_dec EventField_eq_dec field (event_fields named));
    [rewrite Heq by assumption|]; reflexivity.
Qed.

Lemma event_storage_split_field : forall named base image f,
  In f (event_fields named) ->
  event_storage_rep named base image |--
  event_cell base f (image f) ** event_storage_without_field named base image f.
Proof. intros; apply store_fields_split_field; [apply event_fields_nodup|assumption]. Qed.

Lemma event_storage_merge_field : forall named base image f,
  In f (event_fields named) ->
  event_cell base f (image f) ** event_storage_without_field named base image f |--
  event_storage_rep named base image.
Proof. intros; apply store_fields_merge_field; [apply event_fields_nodup|assumption]. Qed.

Lemma event_storage_merge_updated_field : forall named base image f value,
  In f (event_fields named) ->
  event_cell base f value ** event_storage_without_field named base image f |--
  event_storage_rep named base (event_write image f value).
Proof. intros; apply store_fields_merge_updated_field; [apply event_fields_nodup|assumption]. Qed.

Definition event_encode_pool_link (sg : StableGlobVars) (eid : option EventID) : addr :=
  match eid with Some i => event_pool_addr sg i | None => 0 end.

Definition event_set_lifecycle (s : Glob_EventAbstractState) (life : EventLifecycleState)
  : Glob_EventAbstractState :=
  {| inUsedEventStates := s.(inUsedEventStates); unUsedEventStates := s.(unUsedEventStates);
     publishedQueueBytes := s.(publishedQueueBytes); eventLifecycle := life |}.

Definition event_allocated_slots (s : Glob_EventAbstractState)
  : EventID -> option (OSEventAbstractState + EventPrivateAllocation) :=
  fun eid => match s.(eventLifecycle).(eventPrivate) eid with
  | Some a => Some (inr a)
  | None => option_map (@inl OSEventAbstractState EventPrivateAllocation)
      (s.(inUsedEventStates) eid)
  end.

Definition event_pool_partition (sg : StableGlobVars) (s : Glob_EventAbstractState) : Prop :=
  kernel_pool_partition sg.(osMaxEvents) s.(unUsedEventStates) (event_allocated_slots s) /\
  forall eid a, s.(eventLifecycle).(eventPrivate) eid = Some a -> s.(inUsedEventStates) eid = None.

Definition event_free_storage_valid (sg : StableGlobVars)
  (s : Glob_EventAbstractState) : Prop :=
  (forall eid, (exists image, s.(eventLifecycle).(eventFreeStorage) eid = Some image) <->
    In eid s.(unUsedEventStates)) /\
  (forall eid image, s.(eventLifecycle).(eventFreeStorage) eid = Some image ->
    image EventPtrField = Some (event_encode_pool_link sg (kernel_list_next s.(unUsedEventStates) eid))) /\
  (forall eid image, s.(eventLifecycle).(eventFreeStorage) eid = Some image ->
    image EventTypeField = Some 0).

Lemma event_allocated_slots_private : forall s eid a,
  s.(eventLifecycle).(eventPrivate) eid = Some a -> event_allocated_slots s eid = Some (inr a).
Proof. intros; unfold event_allocated_slots; rewrite H; reflexivity. Qed.

Lemma event_pool_free_unallocated : forall sg s eid,
  event_pool_partition sg s -> In eid s.(unUsedEventStates) ->
  s.(inUsedEventStates) eid = None /\ s.(eventLifecycle).(eventPrivate) eid = None.
Proof.
  intros sg s eid [[Hnd [Hr Hpart]] Hdisjoint] Hin.
  assert (Hnone : event_allocated_slots s eid = None).
  { destruct (event_allocated_slots s eid) as [v|] eqn:E; [|reflexivity].
    destruct (proj1 (Hpart eid) (ex_intro _ v E)) as [_ Hnot]; contradiction. }
  unfold event_allocated_slots in Hnone.
  destruct (s.(eventLifecycle).(eventPrivate) eid); [discriminate|].
  destruct (s.(inUsedEventStates) eid); [discriminate|]; split; reflexivity.
Qed.

Lemma event_pool_private_not_free : forall sg s eid a,
  event_pool_partition sg s -> s.(eventLifecycle).(eventPrivate) eid = Some a ->
  valid_event_id sg eid /\ ~ In eid s.(unUsedEventStates) /\ s.(inUsedEventStates) eid = None.
Proof.
  intros sg s eid a [[Hnd [Hr Hpart]] Hdisjoint] Hget.
  destruct (proj1 (Hpart eid) (ex_intro _ (inr a) (event_allocated_slots_private s eid a Hget)))
    as [Hrange Hnot].
  split; [exact Hrange|]. split; [exact Hnot|eapply Hdisjoint; eauto].
Qed.

(** The successful OSEventFreeList pop.  [image] is the old node's actual
    storage.  This transformer does not initialize Type/Cnt/Ptr/bitmap or
    publish a payload; invocation/generation are proof identities. *)
Definition event_detach_head (s : Glob_EventAbstractState) (eid : EventID)
  (rest : list EventID) (image : EventStorage)
  : Glob_EventAbstractState :=
  let life := s.(eventLifecycle) in
  let a := {| eventPrivateInvocation := life.(eventNextInvocation);
              eventPrivateGeneration := life.(eventNextGeneration);
              eventPrivateQueue := None;
              eventPrivateMutexPCP := None;
              eventPrivateStorage := image |} in
  {| inUsedEventStates := s.(inUsedEventStates); unUsedEventStates := rest;
     publishedQueueBytes := s.(publishedQueueBytes);
     eventLifecycle :=
       {| eventFreeStorage := kernel_map_set life.(eventFreeStorage) eid None;
          eventPrivate := kernel_map_set life.(eventPrivate) eid (Some a);
          eventNextGeneration := S life.(eventNextGeneration);
          eventNextInvocation := S life.(eventNextInvocation) |} |}.

Definition event_private_write (s : Glob_EventAbstractState) (eid : EventID)
  (a : EventPrivateAllocation) (f : EventField) (value : option Z)
  : Glob_EventAbstractState :=
  let life := s.(eventLifecycle) in
  event_set_lifecycle s
    {| eventFreeStorage := life.(eventFreeStorage);
       eventPrivate := kernel_map_set life.(eventPrivate) eid
        (Some {| eventPrivateInvocation := a.(eventPrivateInvocation);
                  eventPrivateGeneration := a.(eventPrivateGeneration);
                  eventPrivateQueue := a.(eventPrivateQueue);
                  eventPrivateMutexPCP := a.(eventPrivateMutexPCP);
                  eventPrivateStorage := event_write a.(eventPrivateStorage) f value |});
       eventNextGeneration := life.(eventNextGeneration);
       eventNextInvocation := life.(eventNextInvocation) |}.

(** Records the enabled priority cell already written by MutexCreate.
    This is logical reservation metadata, not a C store or a second owner
    of that cell.  Field stores retain it through event_private_write. *)
Definition event_private_set_mutex_pcp (s : Glob_EventAbstractState) (eid : EventID)
  (allocation : EventPrivateAllocation) (pcp : option Priority) : Glob_EventAbstractState :=
  let life := s.(eventLifecycle) in
  event_set_lifecycle s
    {| eventFreeStorage := life.(eventFreeStorage);
       eventPrivate := kernel_map_set life.(eventPrivate) eid
         (Some {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
                  eventPrivateGeneration := allocation.(eventPrivateGeneration);
                  eventPrivateQueue := allocation.(eventPrivateQueue);
                  eventPrivateMutexPCP := pcp;
                  eventPrivateStorage := allocation.(eventPrivateStorage) |});
       eventNextGeneration := life.(eventNextGeneration);
       eventNextInvocation := life.(eventNextInvocation) |}.

(** A projection of the private ledger, not another stored resource map.
    Ordinary private ECBs are absent from this reservation-only view. *)
Definition event_mutex_lease_view (events : Glob_EventAbstractState)
  (eid : EventID) : option (Priority * option QueueID) :=
  match events.(eventLifecycle).(eventPrivate) eid with
  | Some allocation => match allocation.(eventPrivateMutexPCP) with
      | Some pcp => Some (pcp, allocation.(eventPrivateQueue))
      | None => None
      end
  | None => None
  end.

Definition event_detach_mutex_head (sg : StableGlobVars) (s : Glob_EventAbstractState)
  (eid : EventID) (rest : list EventID) (image : EventStorage) (pcp : Priority)
  : Glob_EventAbstractState :=
  let allocation :=
    {| eventPrivateInvocation := s.(eventLifecycle).(eventNextInvocation);
       eventPrivateGeneration := s.(eventLifecycle).(eventNextGeneration);
       eventPrivateQueue := None; eventPrivateMutexPCP := None; eventPrivateStorage := image |} in
  event_private_set_mutex_pcp (event_detach_head s eid rest image) eid allocation
    (if Z.eqb pcp sg.(osPrioMutexCeilDis) then None else Some pcp).

(** OSQCreate's QCB-exhaustion path writes only the ECB link and the free
    root.  It does not zero the old payload or invent a published event. *)
Definition event_rollback (sg : StableGlobVars) (s : Glob_EventAbstractState)
  (eid : EventID) (a : EventPrivateAllocation) : Glob_EventAbstractState :=
  let life := s.(eventLifecycle) in
  {| inUsedEventStates := s.(inUsedEventStates);
     unUsedEventStates := eid :: s.(unUsedEventStates);
     publishedQueueBytes := s.(publishedQueueBytes);
     eventLifecycle :=
       {| eventFreeStorage := kernel_map_set life.(eventFreeStorage) eid
            (Some (event_write a.(eventPrivateStorage) EventPtrField
              (Some (event_encode_pool_link sg (hd_error s.(unUsedEventStates))))));
          eventPrivate := kernel_map_set life.(eventPrivate) eid None;
          eventNextGeneration := life.(eventNextGeneration);
          eventNextInvocation := life.(eventNextInvocation) |} |}.

Lemma event_detach_head_preserves_partition : forall sg s eid rest image,
  event_pool_partition sg s -> s.(unUsedEventStates) = eid :: rest ->
  event_pool_partition sg (event_detach_head s eid rest image).
Proof.
  intros sg s eid rest image Hvalid Hfree.
  destruct Hvalid as [Hpart Hdisjoint].
  assert (Hnone : s.(inUsedEventStates) eid = None).
  { apply (proj1 (event_pool_free_unallocated sg s eid
      (conj Hpart Hdisjoint) ltac:(rewrite Hfree; left; reflexivity))). }
  assert (Hentries : event_allocated_slots (event_detach_head s eid rest image) =
    kernel_map_set (event_allocated_slots s) eid
      (Some (inr {| eventPrivateInvocation := s.(eventLifecycle).(eventNextInvocation);
                    eventPrivateGeneration := s.(eventLifecycle).(eventNextGeneration);
                    eventPrivateQueue := None;
                    eventPrivateMutexPCP := None;
                    eventPrivateStorage := image |}))).
  { apply functional_extensionality; intro i;
      unfold event_allocated_slots, event_detach_head; simpl;
      unfold kernel_map_set; destruct (Z.eq_dec i eid); reflexivity. }
  split.
  - rewrite Hentries; rewrite Hfree in Hpart.
    exact (kernel_pool_allocate_preserves_partition _ _ _ _ _ _ Hpart).
  - intros i a Hget; simpl in Hget |- *; unfold kernel_map_set in Hget.
    destruct (Z.eq_dec i eid) as [->|Hne]; [exact Hnone|eapply Hdisjoint; exact Hget].
Qed.

Lemma event_private_write_preserves_partition : forall sg s eid a f value,
  event_pool_partition sg s -> s.(eventLifecycle).(eventPrivate) eid = Some a ->
  event_pool_partition sg (event_private_write s eid a f value).
Proof.
  intros sg s eid a f value [Hpart Hdisjoint] Hget.
  assert (Hentries : event_allocated_slots (event_private_write s eid a f value) =
    kernel_map_set (event_allocated_slots s) eid
      (Some (inr {| eventPrivateInvocation := a.(eventPrivateInvocation);
                    eventPrivateGeneration := a.(eventPrivateGeneration);
                    eventPrivateQueue := a.(eventPrivateQueue);
                    eventPrivateMutexPCP := a.(eventPrivateMutexPCP);
                    eventPrivateStorage := event_write a.(eventPrivateStorage) f value |}))).
  { apply functional_extensionality; intro i;
      unfold event_allocated_slots, event_private_write, event_set_lifecycle; simpl;
      unfold kernel_map_set; destruct (Z.eq_dec i eid); reflexivity. }
  split.
  - rewrite Hentries; eapply kernel_pool_replace_preserves_partition;
      [exact Hpart|apply event_allocated_slots_private; exact Hget].
  - intros i b Hb; simpl in Hb |- *; unfold kernel_map_set in Hb;
      destruct (Z.eq_dec i eid) as [->|Hne]; eapply Hdisjoint; eauto.
Qed.

Lemma event_rollback_preserves_partition : forall sg s eid a,
  event_pool_partition sg s -> s.(eventLifecycle).(eventPrivate) eid = Some a ->
  event_pool_partition sg (event_rollback sg s eid a).
Proof.
  intros sg s eid a [Hpart Hdisjoint] Hget.
  pose proof (Hdisjoint eid a Hget) as Hnone.
  assert (Hentries : event_allocated_slots (event_rollback sg s eid a) =
    kernel_map_set (event_allocated_slots s) eid None).
  { apply functional_extensionality; intro i;
      unfold event_allocated_slots, event_rollback; simpl;
      unfold kernel_map_set; destruct (Z.eq_dec i eid) as [->|Hne];
      [rewrite Hnone|]; reflexivity. }
  split.
  - rewrite Hentries; eapply kernel_pool_release_preserves_partition;
      [exact Hpart|apply event_allocated_slots_private; exact Hget].
  - intros i b Hb; simpl in Hb |- *; unfold kernel_map_set in Hb;
      destruct (Z.eq_dec i eid); [discriminate|eapply Hdisjoint; eauto].
Qed.

Lemma event_detach_head_preserves_free_storage : forall sg s eid rest image,
  event_pool_partition sg s -> event_free_storage_valid sg s ->
  s.(unUsedEventStates) = eid :: rest ->
  event_free_storage_valid sg (event_detach_head s eid rest image).
Proof.
  intros sg s eid rest image [[Hnd [Hr Hp]] Hd] [Hdomain [Hlinks Htype]] Hfree.
  rewrite Hfree in Hnd; inversion Hnd as [|? ? Hnot Hrest]; subst.
  split.
  - intro i; simpl; unfold kernel_map_set; destruct (Z.eq_dec i eid) as [->|Hne].
    + split; [intros [v H]; discriminate|intros H; contradiction].
    + rewrite Hdomain, Hfree; simpl; intuition congruence.
  - split.
    + intros i v Hget; simpl in Hget |- *; unfold kernel_map_set in Hget.
      destruct (Z.eq_dec i eid) as [->|Hne]; [discriminate|].
      specialize (Hlinks i v Hget); rewrite Hfree in Hlinks; simpl in Hlinks.
      destruct (Z.eq_dec i eid); [contradiction|exact Hlinks].
    + intros i v Hget; simpl in Hget; unfold kernel_map_set in Hget.
      destruct (Z.eq_dec i eid); [discriminate|eapply Htype; exact Hget].
Qed.

Lemma event_private_write_preserves_free_storage : forall sg s eid a f value,
  event_free_storage_valid sg s ->
  event_free_storage_valid sg (event_private_write s eid a f value).
Proof. intros; exact H. Qed.

Lemma event_rollback_preserves_free_storage : forall sg s eid a,
  event_pool_partition sg s -> event_free_storage_valid sg s ->
  s.(eventLifecycle).(eventPrivate) eid = Some a ->
  a.(eventPrivateStorage) EventTypeField = Some 0 ->
  event_free_storage_valid sg (event_rollback sg s eid a).
Proof.
  intros sg s eid a Hpart [Hdomain [Hlinks Htype]] Hget HtypeA.
  split.
  - intro i; simpl; unfold kernel_map_set; destruct (Z.eq_dec i eid) as [->|Hne].
    + split; [intros _; left; reflexivity|intros _; eexists; reflexivity].
    + rewrite Hdomain; simpl; intuition congruence.
  - split.
    + intros i v Hv; simpl in Hv |- *; unfold kernel_map_set in Hv.
      destruct (Z.eq_dec i eid) as [->|Hne].
      * injection Hv as He; subst v; unfold event_write.
        rewrite field_update_same; simpl; destruct (Z.eq_dec eid eid); [reflexivity|contradiction].
      * simpl; destruct (Z.eq_dec i eid); [contradiction|eapply Hlinks; exact Hv].
    + intros i v Hv; simpl in Hv; unfold kernel_map_set in Hv.
      destruct (Z.eq_dec i eid) as [->|Hne].
      * injection Hv as He; subst v; unfold event_write.
        rewrite field_update_other by discriminate; exact HtypeA.
      * eapply Htype; exact Hv.
Qed.

Definition event_boot_image (sg : StableGlobVars) (ids : list EventID)
  (eid : EventID) : EventStorage :=
  fun f => match f with
  | EventPtrField => Some (event_encode_pool_link sg (kernel_list_next ids eid))
  | _ => Some 0
  end.

(** Names-enabled boot images used by [OS_InitEventList].  The upstream
    initializer writes the same static "?" pointer into every ECB; this
    parameter is that pointer value, not ownership of the bytes it denotes.
    Keeping the name-enabled image separate preserves the historical
    names-disabled endpoint while making the 24-byte layout explicit. *)
Definition event_boot_image_named (sg : StableGlobVars) (ids : list EventID)
  (eid : EventID) (name : addr) : EventStorage :=
  fun f => match f with
  | EventPtrField => Some (event_encode_pool_link sg (kernel_list_next ids eid))
  | EventNameField => Some name
  | _ => Some 0
  end.

Lemma event_boot_image_named_name : forall sg ids eid name,
  event_boot_image_named sg ids eid name EventNameField = Some name.
Proof. intros; reflexivity. Qed.

Lemma event_boot_image_named_non_name : forall sg ids eid name field,
  field <> EventNameField ->
  event_boot_image_named sg ids eid name field = event_boot_image sg ids eid field.
Proof.
  intros sg ids eid name field Hfield.
  destruct field; try reflexivity; contradiction.
Qed.

(** Post-state of clearing the selected ECB array and writing its free
    links.  Conditional EventName initialization is not claimed here. *)
Definition event_pool_initial (sg : StableGlobVars) : Glob_EventAbstractState :=
  let ids := Zrange 0 sg.(osMaxEvents) in
  {| inUsedEventStates := fun _ => None; unUsedEventStates := ids;
     publishedQueueBytes := fun _ => None;
     eventLifecycle :=
       {| eventFreeStorage := fun eid => if in_dec Z.eq_dec eid ids
            then Some (event_boot_image sg ids eid) else None;
          eventPrivate := fun _ => None; eventNextGeneration := 0;
          eventNextInvocation := 0 |} |}.

(** Names-enabled counterpart of [event_pool_initial].  It is deliberately a
    separate endpoint: switching the ECB layout changes the concrete bytes,
    so a names-disabled proof must not be silently reused. *)
Definition event_pool_initial_named (sg : StableGlobVars) (name : addr)
  : Glob_EventAbstractState :=
  let ids := Zrange 0 sg.(osMaxEvents) in
  {| inUsedEventStates := fun _ => None; unUsedEventStates := ids;
     publishedQueueBytes := fun _ => None;
     eventLifecycle :=
       {| eventFreeStorage := fun eid => if in_dec Z.eq_dec eid ids
            then Some (event_boot_image_named sg ids eid name) else None;
          eventPrivate := fun _ => None; eventNextGeneration := 0;
          eventNextInvocation := 0 |} |}.

Lemma event_pool_initial_partition : forall sg,
  event_pool_partition sg (event_pool_initial sg).
Proof.
  intros; split; [apply kernel_pool_initial_partition|intros; discriminate].
Qed.

Lemma event_pool_initial_free_storage : forall sg,
  event_free_storage_valid sg (event_pool_initial sg).
Proof.
  intro sg; split.
  - intro eid; simpl; destruct (in_dec Z.eq_dec eid (Zrange 0 (osMaxEvents sg))) as [Hin|Hnot].
    + split; [intros _; exact Hin|intros _; eexists; reflexivity].
    + split; [intros [v H]; discriminate|contradiction].
  - split; intros eid image Hget; simpl in Hget.
    all: destruct (in_dec Z.eq_dec eid (Zrange 0 (osMaxEvents sg))); try discriminate.
    all: injection Hget as He; subst image; reflexivity.
Qed.

Lemma event_pool_initial_named_partition : forall sg name,
  event_pool_partition sg (event_pool_initial_named sg name).
Proof.
  intros; split; [apply kernel_pool_initial_partition|intros; discriminate].
Qed.

Lemma event_pool_initial_named_free_storage : forall sg name,
  event_free_storage_valid sg (event_pool_initial_named sg name).
Proof.
  intros sg name; split.
  - intro eid; simpl; destruct (in_dec Z.eq_dec eid (Zrange 0 (osMaxEvents sg))) as [Hin|Hnot].
    + split; [intros _; exact Hin|intros _; eexists; reflexivity].
    + split; [intros [v H]; discriminate|contradiction].
  - split; intros eid image Hget; simpl in Hget.
    all: destruct (in_dec Z.eq_dec eid (Zrange 0 (osMaxEvents sg))); try discriminate.
    all: injection Hget as He; subst image; reflexivity.
Qed.

Definition event_free_storage_rep (sg : StableGlobVars)
  (s : Glob_EventAbstractState) : Assertion :=
  store_map (fun eid image => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image)
    s.(eventLifecycle).(eventFreeStorage).

Definition event_free_root_rep (sg : StableGlobVars)
  (s : Glob_EventAbstractState) : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error s.(unUsedEventStates)).

Definition event_private_storage_rep (sg : StableGlobVars)
  (eid : EventID) (a : EventPrivateAllocation) : Assertion :=
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) a.(eventPrivateStorage).

(** An invocation-filtered view of the existing private map, not another
    stored ownership table.  Event invocation numbers belong to the Event
    allocator namespace; the critical-region protocol carries the Task call context. *)
Definition event_creation_view (events : Glob_EventAbstractState) (invocation : nat)
  : EventID -> option EventPrivateAllocation :=
  fun eid => match events.(eventLifecycle).(eventPrivate) eid with
  | Some allocation => if Nat.eq_dec allocation.(eventPrivateInvocation) invocation
      then Some allocation else None
  | None => None
  end.

Definition event_creation_frame (invocation : nat)
  (before after : Glob_EventAbstractState) : Prop :=
  event_creation_view after invocation = event_creation_view before invocation.

Definition event_creation_storage (sg : StableGlobVars)
  (events : Glob_EventAbstractState) (invocation : nat) : Assertion :=
  store_map (event_private_storage_rep sg) (event_creation_view events invocation).

Lemma event_creation_frame_lookup : forall invocation before after eid allocation,
  event_creation_frame invocation before after ->
  before.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = invocation ->
  after.(eventLifecycle).(eventPrivate) eid = Some allocation.
Proof.
  intros invocation before after eid allocation Hframe Hget Hinv.
  pose proof (f_equal (fun view => view eid) Hframe) as Heq.
  unfold event_creation_view in Heq; rewrite Hget in Heq.
  destruct (Nat.eq_dec allocation.(eventPrivateInvocation) invocation); [|contradiction].
  destruct (after.(eventLifecycle).(eventPrivate) eid) as [other|] eqn:Hother;
    [destruct (Nat.eq_dec other.(eventPrivateInvocation) invocation)|]; congruence.
Qed.

(** Predicate reindexing only: it neither allocates the private bytes nor
    proves a C callee's footprint.  The source callee still needs its
    actual spatial contract and QCP's ordinary separating frame rule. *)
Lemma event_creation_frame_storage_eq : forall sg invocation before after,
  event_creation_frame invocation before after ->
  event_creation_storage sg after invocation = event_creation_storage sg before invocation.
Proof. intros; unfold event_creation_storage; rewrite H; reflexivity. Qed.

Lemma event_creation_frame_map_eq : forall invocation before after,
  after.(eventLifecycle).(eventPrivate) = before.(eventLifecycle).(eventPrivate) ->
  event_creation_frame invocation before after.
Proof. intros; unfold event_creation_frame, event_creation_view; rewrite H; reflexivity. Qed.

Lemma event_creation_view_update_foreign : forall before after eid observer,
  (forall other, other <> eid -> after.(eventLifecycle).(eventPrivate) other =
    before.(eventLifecycle).(eventPrivate) other) ->
  (forall allocation, before.(eventLifecycle).(eventPrivate) eid = Some allocation ->
    allocation.(eventPrivateInvocation) <> observer) ->
  (forall allocation, after.(eventLifecycle).(eventPrivate) eid = Some allocation ->
    allocation.(eventPrivateInvocation) <> observer) ->
  event_creation_frame observer before after.
Proof.
  intros before after eid observer Hother Hbefore Hafter.
  unfold event_creation_frame; apply functional_extensionality; intro slot.
  unfold event_creation_view; destruct (Z.eq_dec slot eid) as [->|Hne].
  - assert (Hfilter : forall candidate : option EventPrivateAllocation,
      (forall allocation, candidate = Some allocation -> allocation.(eventPrivateInvocation) <> observer) ->
      (match candidate with Some allocation =>
         if Nat.eq_dec allocation.(eventPrivateInvocation) observer then Some allocation else None
       | None => None end) = None).
    { intros [allocation|] Hforeign; [|reflexivity].
      destruct (Nat.eq_dec allocation.(eventPrivateInvocation) observer) as [Heq|Hne]; [|reflexivity].
      exfalso; exact (Hforeign allocation eq_refl Heq). }
    rewrite (Hfilter _ Hafter), (Hfilter _ Hbefore); reflexivity.
  - rewrite Hother by exact Hne; reflexivity.
Qed.

Lemma event_detach_frames_other_invocation : forall events eid rest image observer,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  events.(eventLifecycle).(eventNextInvocation) <> observer ->
  event_creation_frame observer events (event_detach_head events eid rest image).
Proof.
  intros events eid rest image observer Hnone Hforeign.
  eapply event_creation_view_update_foreign with (eid := eid).
  - intros; simpl; apply kernel_map_set_other; assumption.
  - intros allocation Hget; congruence.
  - intros allocation Hget; simpl in Hget; rewrite kernel_map_set_same in Hget.
    injection Hget as Hget; subst allocation; exact Hforeign.
Qed.

Lemma event_private_write_frames_other_invocation : forall events eid allocation field stored observer,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer events (event_private_write events eid allocation field stored).
Proof.
  intros events eid allocation field stored observer Hget Hforeign.
  eapply event_creation_view_update_foreign with (eid := eid).
  - intros; simpl; apply kernel_map_set_other; assumption.
  - intros other Hother; congruence.
  - intros other Hother; simpl in Hother; rewrite kernel_map_set_same in Hother.
    injection Hother as Hother; subst other; exact Hforeign.
Qed.

Lemma event_rollback_frames_other_invocation : forall sg events eid allocation observer,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer events (event_rollback sg events eid allocation).
Proof.
  intros sg events eid allocation observer Hget Hforeign.
  eapply event_creation_view_update_foreign with (eid := eid).
  - intros; simpl; apply kernel_map_set_other; assumption.
  - intros other Hother; congruence.
  - intros other Hother; simpl in Hother; rewrite kernel_map_set_same in Hother; discriminate.
Qed.

Definition event_free_storage_without_eid (sg : StableGlobVars)
  (s : Glob_EventAbstractState) (eid : EventID) : Assertion :=
  store_map_missing_i
    (fun i image => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg i) image)
    s.(eventLifecycle).(eventFreeStorage) eid.

Lemma event_free_storage_split_eid : forall sg s eid image,
  s.(eventLifecycle).(eventFreeStorage) eid = Some image ->
  event_free_storage_rep sg s |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
  event_free_storage_without_eid sg s eid.
Proof.
  intros; unfold event_free_storage_rep, event_free_storage_without_eid.
  sep_apply_l_atomic (store_map_split
    (fun i value => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg i) value)
    eid image _ H); entailer!.
Qed.

Lemma event_free_storage_merge_eid : forall sg s eid image,
  s.(eventLifecycle).(eventFreeStorage) eid = Some image ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
  event_free_storage_without_eid sg s eid |-- event_free_storage_rep sg s.
Proof.
  intros; unfold event_free_storage_rep, event_free_storage_without_eid.
  sep_apply_l_atomic (store_map_merge
    (fun i value => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg i) value)
    eid image _ H); entailer!.
Qed.

Lemma event_free_storage_remove_eid_equiv : forall sg before after eid,
  after.(eventLifecycle).(eventFreeStorage) eid = None ->
  (forall other, other <> eid -> before.(eventLifecycle).(eventFreeStorage) other =
    after.(eventLifecycle).(eventFreeStorage) other) ->
  event_free_storage_without_eid sg before eid --||--
  event_free_storage_rep sg after.
Proof.
  intros sg before after eid Hnone Hframe.
  unfold event_free_storage_without_eid, event_free_storage_rep.
  destruct (store_map_missing_i_equiv
    (fun i value => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg i) value)
    _ _ eid Hframe) as [Hforward Hbackward].
  split.
  - eapply derivable1_trans; [exact Hforward|apply store_map_missing_equiv_store_map; exact Hnone].
  - eapply derivable1_trans; [apply store_map_equiv_store_map_missing; exact Hnone|exact Hbackward].
Qed.

Lemma event_free_storage_merge_added_eid : forall sg before after eid image,
  before.(eventLifecycle).(eventFreeStorage) eid = None ->
  after.(eventLifecycle).(eventFreeStorage) eid = Some image ->
  (forall other, other <> eid -> before.(eventLifecycle).(eventFreeStorage) other =
    after.(eventLifecycle).(eventFreeStorage) other) ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
  event_free_storage_rep sg before |-- event_free_storage_rep sg after.
Proof.
  intros sg before after eid image Hnone Hget Hframe.
  unfold event_free_storage_rep.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (fun i value => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg i) value) _ eid Hnone).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun i value => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg i) value) _ _ eid Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun i value => event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg i) value) eid image _ Hget).
  entailer!.
Qed.

(** The root cell on the left already contains the value written by the
    source pop.  The old ECB image is transferred intact to the caller. *)
Lemma event_detach_head_reconstructs_storage : forall sg s eid rest image,
  s.(eventLifecycle).(eventFreeStorage) eid = Some image ->
  event_free_storage_rep sg s **
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
  event_free_storage_rep sg (event_detach_head s eid rest image) **
  event_free_root_rep sg (event_detach_head s eid rest image).
Proof.
  intros sg s eid rest image Hget.
  sep_apply_l_atomic (event_free_storage_split_eid sg s eid image Hget).
  sep_apply_l_atomic (proj1 (event_free_storage_remove_eid_equiv sg s
    (event_detach_head s eid rest image) eid
    ltac:(simpl; apply kernel_map_set_same)
    ltac:(intros; simpl; symmetry; apply kernel_map_set_other; assumption))).
  unfold event_free_root_rep; simpl; entailer!.
Qed.

(** The private Ptr cell and the free root must both have undergone the
    source writes.  Everything else in the ECB remains in the residual. *)
Lemma event_rollback_reconstructs_storage : forall sg s eid a,
  event_pool_partition sg s -> event_free_storage_valid sg s ->
  s.(eventLifecycle).(eventPrivate) eid = Some a ->
  event_cell (event_pool_addr sg eid) EventPtrField
    (Some (event_encode_pool_link sg (hd_error s.(unUsedEventStates)))) **
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) a.(eventPrivateStorage) EventPtrField **
  event_free_storage_rep sg s **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid |--
  event_free_storage_rep sg (event_rollback sg s eid a) **
  event_free_root_rep sg (event_rollback sg s eid a).
Proof.
  intros sg s eid a Hpart [Hdomain Hlinks] Hget.
  destruct (event_pool_private_not_free sg s eid a Hpart Hget) as [_ [Hnot Hnone]].
  assert (HstorageNone : s.(eventLifecycle).(eventFreeStorage) eid = None).
  { destruct (s.(eventLifecycle).(eventFreeStorage) eid) as [image|] eqn:E; [|reflexivity].
    exfalso; apply Hnot; apply (proj1 (Hdomain eid)); eauto. }
  sep_apply_l_atomic (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    a.(eventPrivateStorage) EventPtrField
    (Some (event_encode_pool_link sg (hd_error s.(unUsedEventStates))))
    ltac:(simpl; tauto)).
  sep_apply_l_atomic (event_free_storage_merge_added_eid sg s
    (event_rollback sg s eid a) eid _ HstorageNone
    ltac:(simpl; apply kernel_map_set_same)
    ltac:(intros; simpl; symmetry; apply kernel_map_set_other; assumption)).
  unfold event_free_root_rep; simpl; entailer!.
Qed.

Definition event_publish (s : Glob_EventAbstractState) (eid : EventID)
  (node : OSEventAbstractState) : Glob_EventAbstractState :=
  let life := s.(eventLifecycle) in
  {| inUsedEventStates := kernel_map_set s.(inUsedEventStates) eid (Some node);
     unUsedEventStates := s.(unUsedEventStates); publishedQueueBytes := s.(publishedQueueBytes);
     eventLifecycle :=
       {| eventFreeStorage := life.(eventFreeStorage);
          eventPrivate := kernel_map_set life.(eventPrivate) eid None;
          eventNextGeneration := life.(eventNextGeneration);
          eventNextInvocation := life.(eventNextInvocation) |} |}.

Lemma event_publish_preserves_partition : forall sg s eid a node,
  event_pool_partition sg s -> s.(eventLifecycle).(eventPrivate) eid = Some a ->
  event_pool_partition sg (event_publish s eid node).
Proof.
  intros sg s eid a node [Hpart Hdisjoint] Hget.
  assert (Hentries : event_allocated_slots (event_publish s eid node) =
    kernel_map_set (event_allocated_slots s) eid (Some (inl node))).
  { apply functional_extensionality; intro i;
      unfold event_allocated_slots, event_publish; simpl; unfold kernel_map_set;
      destruct (Z.eq_dec i eid); reflexivity. }
  split.
  - rewrite Hentries; eapply kernel_pool_replace_preserves_partition;
      [exact Hpart|apply event_allocated_slots_private; exact Hget].
  - intros i b Hb; simpl in Hb |- *; unfold kernel_map_set in Hb |- *.
    destruct (Z.eq_dec i eid); [discriminate|eapply Hdisjoint; exact Hb].
Qed.

Lemma event_publish_preserves_free_storage : forall sg s eid node,
  event_free_storage_valid sg s ->
  event_free_storage_valid sg (event_publish s eid node).
Proof. intros; exact H. Qed.

Lemma event_publish_frames_other_invocation : forall events eid allocation node observer,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer events (event_publish events eid node).
Proof.
  intros events eid allocation node observer Hget Hforeign.
  eapply event_creation_view_update_foreign with (eid := eid).
  - intros; simpl; apply kernel_map_set_other; assumption.
  - intros other Hother; congruence.
  - intros other Hother; simpl in Hother; rewrite kernel_map_set_same in Hother; discriminate.
Qed.

(** Generations distinguish successive occupants of one physical ECB slot.
    Invocation identity distinguishes concurrent private creations.  These
    observations do not own bytes or make a stale C pointer safe to use. *)
Definition event_slot_generation (s : Glob_EventAbstractState) (eid : EventID)
  : option nat :=
  option_map (fun entry => match entry with
    | inl node => node.(eventGeneration)
    | inr allocation => allocation.(eventPrivateGeneration)
    end) (event_allocated_slots s eid).

Definition event_private_invocation (s : Glob_EventAbstractState) (eid : EventID)
  : option nat :=
  option_map eventPrivateInvocation (s.(eventLifecycle).(eventPrivate) eid).

Definition event_identity_valid (s : Glob_EventAbstractState) : Prop :=
  (forall eid generation, event_slot_generation s eid = Some generation ->
    (generation < s.(eventLifecycle).(eventNextGeneration))%nat) /\
  (forall first second generation,
    event_slot_generation s first = Some generation ->
    event_slot_generation s second = Some generation -> first = second) /\
  (forall eid invocation, event_private_invocation s eid = Some invocation ->
    (invocation < s.(eventLifecycle).(eventNextInvocation))%nat) /\
  (forall first second invocation,
    event_private_invocation s first = Some invocation ->
    event_private_invocation s second = Some invocation -> first = second).

Lemma event_identity_valid_from_submap : forall before after,
  event_identity_valid before ->
  (before.(eventLifecycle).(eventNextGeneration) <=
    after.(eventLifecycle).(eventNextGeneration))%nat ->
  (before.(eventLifecycle).(eventNextInvocation) <=
    after.(eventLifecycle).(eventNextInvocation))%nat ->
  (forall eid generation, event_slot_generation after eid = Some generation ->
    event_slot_generation before eid = Some generation) ->
  (forall eid invocation, event_private_invocation after eid = Some invocation ->
    event_private_invocation before eid = Some invocation) ->
  event_identity_valid after.
Proof.
  intros before after [Hgb [Hgu [Hib Hiu]]] Hg Hi Hgens Hinvs.
  split.
  - intros eid generation Hget; specialize (Hgb eid generation (Hgens _ _ Hget)); lia.
  - split.
    + intros; eapply Hgu; eauto.
    + split.
      * intros eid invocation Hget; specialize (Hib eid invocation (Hinvs _ _ Hget)); lia.
      * intros; eapply Hiu; eauto.
Qed.

Lemma event_pool_initial_identity_valid : forall sg,
  event_identity_valid (event_pool_initial sg).
Proof. intros; repeat split; intros; discriminate. Qed.

Lemma event_pool_initial_named_identity_valid : forall sg name,
  event_identity_valid (event_pool_initial_named sg name).
Proof. intros; repeat split; intros; discriminate. Qed.

Lemma event_detach_head_preserves_identity : forall s eid rest image,
  event_identity_valid s ->
  event_identity_valid (event_detach_head s eid rest image).
Proof.
  intros s eid rest image [Hgb [Hgu [Hib Hiu]]].
  assert (Hgen : forall i,
    event_slot_generation (event_detach_head s eid rest image) i =
    if Z.eq_dec i eid then Some s.(eventLifecycle).(eventNextGeneration)
    else event_slot_generation s i).
  { intro i; unfold event_slot_generation, event_allocated_slots,
      event_detach_head; simpl; unfold kernel_map_set;
      destruct (Z.eq_dec i eid); reflexivity. }
  assert (Hinv : forall i,
    event_private_invocation (event_detach_head s eid rest image) i =
    if Z.eq_dec i eid then Some s.(eventLifecycle).(eventNextInvocation)
    else event_private_invocation s i).
  { intro i; unfold event_private_invocation, event_detach_head; simpl;
      unfold kernel_map_set; destruct (Z.eq_dec i eid); reflexivity. }
  split.
  - intros i generation Hget; rewrite Hgen in Hget; simpl.
    destruct (Z.eq_dec i eid); [injection Hget as He; subst generation; lia|].
    specialize (Hgb i generation Hget); lia.
  - split.
    + intros i j generation Hi Hj; rewrite Hgen in Hi, Hj.
      destruct (Z.eq_dec i eid) as [->|Hine];
        destruct (Z.eq_dec j eid) as [->|Hjne]; [reflexivity| | |].
      * injection Hi as He; subst generation; specialize (Hgb j _ Hj); lia.
      * injection Hj as He; subst generation; specialize (Hgb i _ Hi); lia.
      * eapply Hgu; eauto.
    + split.
      * intros i invocation Hget; rewrite Hinv in Hget; simpl.
        destruct (Z.eq_dec i eid); [injection Hget as He; subst invocation; lia|].
        specialize (Hib i invocation Hget); lia.
      * intros i j invocation Hi Hj; rewrite Hinv in Hi, Hj.
        destruct (Z.eq_dec i eid) as [->|Hine];
          destruct (Z.eq_dec j eid) as [->|Hjne]; [reflexivity| | |].
        -- injection Hi as He; subst invocation; specialize (Hib j _ Hj); lia.
        -- injection Hj as He; subst invocation; specialize (Hib i _ Hi); lia.
        -- eapply Hiu; eauto.
Qed.

Lemma event_private_write_preserves_identity : forall s eid a f value,
  event_identity_valid s -> s.(eventLifecycle).(eventPrivate) eid = Some a ->
  event_identity_valid (event_private_write s eid a f value).
Proof.
  intros s eid a f value Hvalid Hget.
  eapply event_identity_valid_from_submap;
    [exact Hvalid|apply Nat.le_refl|apply Nat.le_refl| |].
  - intros i generation Hi; unfold event_slot_generation, event_allocated_slots,
      event_private_write, event_set_lifecycle in Hi |- *; simpl in Hi.
    unfold kernel_map_set in Hi; destruct (Z.eq_dec i eid) as [->|Hne];
      [rewrite Hget|]; exact Hi.
  - intros i invocation Hi; unfold event_private_invocation,
      event_private_write, event_set_lifecycle in Hi |- *; simpl in Hi.
    unfold kernel_map_set in Hi; destruct (Z.eq_dec i eid) as [->|Hne];
      [rewrite Hget|]; exact Hi.
Qed.

Lemma event_rollback_preserves_identity : forall sg s eid a,
  event_identity_valid s ->
  s.(inUsedEventStates) eid = None ->
  event_identity_valid (event_rollback sg s eid a).
Proof.
  intros sg s eid a Hvalid Hnone.
  eapply event_identity_valid_from_submap;
    [exact Hvalid|apply Nat.le_refl|apply Nat.le_refl| |].
  - intros i generation Hi; unfold event_slot_generation, event_allocated_slots,
      event_rollback in Hi; simpl in Hi; unfold kernel_map_set in Hi.
    destruct (Z.eq_dec i eid) as [->|Hne]; [rewrite Hnone in Hi; discriminate|exact Hi].
  - intros i invocation Hi; unfold event_private_invocation,
      event_rollback in Hi; simpl in Hi; unfold kernel_map_set in Hi.
    destruct (Z.eq_dec i eid); [discriminate|exact Hi].
Qed.

(** Publication preserves the identity acquired at detach; merely putting
    an arbitrary well-typed payload in the used map is not sufficient. *)
Lemma event_publish_preserves_identity : forall s eid a node,
  event_identity_valid s -> s.(eventLifecycle).(eventPrivate) eid = Some a ->
  node.(eventGeneration) = a.(eventPrivateGeneration) ->
  event_identity_valid (event_publish s eid node).
Proof.
  intros s eid a node Hvalid Hget Hgeneration.
  eapply event_identity_valid_from_submap;
    [exact Hvalid|apply Nat.le_refl|apply Nat.le_refl| |].
  - intros i generation Hi; unfold event_slot_generation, event_allocated_slots,
      event_publish in Hi |- *; simpl in Hi; unfold kernel_map_set in Hi.
    destruct (Z.eq_dec i eid) as [->|Hne].
    + rewrite Hget; simpl in Hi |- *; rewrite Hgeneration in Hi; exact Hi.
    + exact Hi.
  - intros i invocation Hi; unfold event_private_invocation,
      event_publish in Hi; simpl in Hi; unfold kernel_map_set in Hi.
    destruct (Z.eq_dec i eid); [discriminate|exact Hi].
Qed.

Lemma event_pool_used_not_free : forall sg s eid node,
  event_pool_partition sg s -> s.(inUsedEventStates) eid = Some node ->
  valid_event_id sg eid /\ ~ In eid s.(unUsedEventStates) /\
  s.(eventLifecycle).(eventPrivate) eid = None.
Proof.
  intros sg s eid node [[Hnd [Hr Hpart]] Hdisjoint] Hget.
  assert (Hprivate : s.(eventLifecycle).(eventPrivate) eid = None).
  { destruct (s.(eventLifecycle).(eventPrivate) eid) as [a|] eqn:E; [|reflexivity].
    pose proof (Hdisjoint eid a E); congruence. }
  assert (Hslot : event_allocated_slots s eid = Some (inl node)).
  { unfold event_allocated_slots; rewrite Hprivate, Hget; reflexivity. }
  destruct (proj1 (Hpart eid) (ex_intro _ (inl node) Hslot)) as [Hrange Hnot].
  split; [exact Hrange|]. split; assumption.
Qed.

(** Selected names-disabled Sem/Mbox/Queue deletion tail: Type := UNUSED,
    Ptr := the current free root, Cnt := 0, then free-root publication.
    Waiter removal and QCB/buffer release precede this ECB-only operation;
    they are not silently performed by this pool transformer. *)
Definition event_recycle_image (sg : StableGlobVars)
  (free : list EventID) (image : EventStorage) : EventStorage :=
  event_write
    (event_write (event_write image EventTypeField (Some 0))
      EventPtrField (Some (event_encode_pool_link sg (hd_error free))))
    EventCntField (Some 0).

Definition event_recycle (sg : StableGlobVars) (s : Glob_EventAbstractState)
  (eid : EventID) (image : EventStorage) : Glob_EventAbstractState :=
  let life := s.(eventLifecycle) in
  {| inUsedEventStates := kernel_map_set s.(inUsedEventStates) eid None;
     unUsedEventStates := eid :: s.(unUsedEventStates);
     publishedQueueBytes := s.(publishedQueueBytes);
     eventLifecycle :=
       {| eventFreeStorage := kernel_map_set life.(eventFreeStorage) eid
            (Some (event_recycle_image sg s.(unUsedEventStates) image));
          eventPrivate := life.(eventPrivate);
          eventNextGeneration := life.(eventNextGeneration);
          eventNextInvocation := life.(eventNextInvocation) |} |}.

Lemma event_recycle_preserves_partition : forall sg s eid node image,
  event_pool_partition sg s -> s.(inUsedEventStates) eid = Some node ->
  event_pool_partition sg (event_recycle sg s eid image).
Proof.
  intros sg s eid node image Hvalid Hget.
  destruct (event_pool_used_not_free sg s eid node Hvalid Hget)
    as [_ [_ Hprivate]].
  destruct Hvalid as [Hpart Hdisjoint].
  assert (Hslot : event_allocated_slots s eid = Some (inl node)).
  { unfold event_allocated_slots; rewrite Hprivate, Hget; reflexivity. }
  assert (Hentries : event_allocated_slots (event_recycle sg s eid image) =
    kernel_map_set (event_allocated_slots s) eid None).
  { apply functional_extensionality; intro i;
      unfold event_allocated_slots, event_recycle; simpl; unfold kernel_map_set;
      destruct (Z.eq_dec i eid) as [->|Hne]; [rewrite Hprivate|]; reflexivity. }
  split.
  - rewrite Hentries; eapply kernel_pool_release_preserves_partition; eauto.
  - intros i a Hi; simpl in Hi |- *; unfold kernel_map_set.
    destruct (Z.eq_dec i eid); [reflexivity|eapply Hdisjoint; exact Hi].
Qed.

Lemma event_recycle_preserves_free_storage : forall sg s eid image,
  event_free_storage_valid sg s ->
  event_free_storage_valid sg (event_recycle sg s eid image).
Proof.
  intros sg s eid image [Hdomain [Hlinks Htype]].
  split.
  - intro i; simpl; unfold kernel_map_set; destruct (Z.eq_dec i eid) as [->|Hne].
    + split; [intros _; left; reflexivity|intros _; eexists; reflexivity].
    + rewrite Hdomain; simpl; intuition congruence.
  - split.
    + intros i v Hv; simpl in Hv |- *; unfold kernel_map_set in Hv.
      destruct (Z.eq_dec i eid) as [->|Hne].
      * injection Hv as He; subst v; unfold event_recycle_image, event_write.
        rewrite field_update_other by discriminate; rewrite field_update_same.
        simpl; destruct (Z.eq_dec eid eid); [reflexivity|contradiction].
      * simpl; destruct (Z.eq_dec i eid); [contradiction|eapply Hlinks; exact Hv].
    + intros i v Hv; simpl in Hv; unfold kernel_map_set in Hv.
      destruct (Z.eq_dec i eid) as [->|Hne].
      * injection Hv as He; subst v; reflexivity.
      * eapply Htype; exact Hv.
Qed.

Lemma event_recycle_preserves_identity : forall sg s eid image,
  event_identity_valid s ->
  event_identity_valid (event_recycle sg s eid image).
Proof.
  intros sg s eid image Hvalid.
  eapply event_identity_valid_from_submap;
    [exact Hvalid|apply Nat.le_refl|apply Nat.le_refl| |].
  - intros i generation Hi; unfold event_slot_generation, event_allocated_slots,
      event_recycle in Hi |- *; simpl in Hi.
    destruct (s.(eventLifecycle).(eventPrivate) i); [exact Hi|].
    unfold kernel_map_set in Hi; destruct (Z.eq_dec i eid); [discriminate|exact Hi].
  - intros i invocation Hi; exact Hi.
Qed.

Lemma event_recycle_reconstructs_free_storage : forall sg s eid node image,
  event_pool_partition sg s -> event_free_storage_valid sg s ->
  s.(inUsedEventStates) eid = Some node ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg s.(unUsedEventStates) image) **
  event_free_storage_rep sg s **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid |--
  event_free_storage_rep sg (event_recycle sg s eid image) **
  event_free_root_rep sg (event_recycle sg s eid image).
Proof.
  intros sg s eid node image Hpart [Hdomain Hrest] Hget.
  destruct (event_pool_used_not_free sg s eid node Hpart Hget) as [_ [Hnot Hprivate]].
  assert (Hnone : s.(eventLifecycle).(eventFreeStorage) eid = None).
  { destruct (s.(eventLifecycle).(eventFreeStorage) eid) as [v|] eqn:E; [|reflexivity].
    exfalso; apply Hnot; apply (proj1 (Hdomain eid)); eauto. }
  sep_apply_l_atomic (event_free_storage_merge_added_eid sg s
    (event_recycle sg s eid image) eid _ Hnone
    ltac:(simpl; apply kernel_map_set_same)
    ltac:(intros; simpl; symmetry; apply kernel_map_set_other; assumption)).
  unfold event_free_root_rep; simpl; entailer!.
Qed.

(** Finite row-to-field adapter for the selected eight-row ECB layout.
    All C array consumers prove 0 <= row < 8; the total default is only a
    Coq value and does not authorize an out-of-bounds C access. *)
Definition event_table_field (row : Z) : EventField :=
  match row with
  | 0 => EventTbl0 | 1 => EventTbl1 | 2 => EventTbl2 | 3 => EventTbl3
  | 4 => EventTbl4 | 5 => EventTbl5 | 6 => EventTbl6 | _ => EventTbl7
  end.

Lemma event_table_field_in_fields : forall named row,
  In (event_table_field row) (event_fields named).
Proof.
  intros named row; unfold event_table_field.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
    unfold event_fields; simpl; tauto.
Qed.

Lemma event_table_field_not_group : forall row,
  event_table_field row <> EventGrpField.
Proof.
  intros row; unfold event_table_field.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; discriminate.
Qed.

Lemma event_table_field_offset_eq : forall row,
  0 <= row < 8 -> event_field_offset (event_table_field row) = 11 + row.
Proof.
  intros row Hrow.
  assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
    row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; subst row; reflexivity.
Qed.

Lemma event_table_field_injective : forall first second,
  0 <= first < 8 -> 0 <= second < 8 ->
  event_table_field first = event_table_field second -> first = second.
Proof.
  intros first second Hfirst Hsecond Heq.
  pose proof (f_equal event_field_offset Heq) as Hoffset.
  change (event_field_offset (event_table_field first) =
    event_field_offset (event_table_field second)) in Hoffset.
  rewrite !event_table_field_offset_eq in Hoffset by assumption; lia.
Qed.

Lemma event_table_cell_eq : forall base row value,
  0 <= row < 8 -> event_cell base (event_table_field row) (Some value) =
    (base + (11 + row)) # UChar |-> value.
Proof.
  intros base row value Hrow.
  assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
    row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; subst row; reflexivity.
Qed.

(** OS_EventWaitListInit stores Grp first, then each OS_PRIO table row.
    The current native profile has eight UChar rows.  This is a typed
    store loop, not OS_MemClr, and leaves Type/Cnt/Ptr/name/padding intact. *)
Fixpoint event_wait_table_init_prefix (image : EventStorage) (count : nat)
  : EventStorage :=
  match count with
  | O => image
  | S previous => event_write (event_wait_table_init_prefix image previous)
      (event_table_field (Z.of_nat previous)) (Some 0)
  end.

Definition event_wait_list_init_image (image : EventStorage) : EventStorage :=
  event_wait_table_init_prefix (event_write image EventGrpField (Some 0)) 8.

Lemma event_wait_table_init_prefix_lookup : forall count image row,
  (count <= 8)%nat -> 0 <= row < Z.of_nat count ->
  event_wait_table_init_prefix image count (event_table_field row) = Some 0.
Proof.
  induction count as [|count IH]; intros image row Hcount Hrow; [simpl in Hrow; lia|].
  cbn [event_wait_table_init_prefix].
  destruct (Z.eq_dec row (Z.of_nat count)) as [->|Hne].
  - apply field_update_same.
  - unfold event_write; rewrite field_update_other.
    + apply IH; lia.
    + intro Heq; apply Hne; eapply event_table_field_injective; [| |exact Heq]; lia.
Qed.

Lemma event_wait_table_init_prefix_frame : forall count image field,
  (forall row, 0 <= row < Z.of_nat count -> field <> event_table_field row) ->
  event_wait_table_init_prefix image count field = image field.
Proof.
  induction count as [|count IH]; intros image field Hframe; [reflexivity|].
  cbn [event_wait_table_init_prefix]; unfold event_write; rewrite field_update_other.
  - apply IH; intros row Hrow; apply Hframe; lia.
  - apply Hframe; lia.
Qed.

Lemma event_wait_list_init_group : forall image,
  event_wait_list_init_image image EventGrpField = Some 0.
Proof. reflexivity. Qed.

Lemma event_wait_list_init_table : forall image row,
  0 <= row < 8 -> event_wait_list_init_image image (event_table_field row) = Some 0.
Proof. intros; apply event_wait_table_init_prefix_lookup; [lia|exact H]. Qed.

Lemma event_wait_list_init_frame : forall image field,
  field <> EventGrpField ->
  (forall row, 0 <= row < 8 -> field <> event_table_field row) ->
  event_wait_list_init_image image field = image field.
Proof.
  intros image field Hgroup Hrows; unfold event_wait_list_init_image.
  rewrite event_wait_table_init_prefix_frame by exact Hrows.
  apply field_update_other; exact Hgroup.
Qed.

Lemma event_wait_table_init_merge_row : forall named base image count,
  (count < 8)%nat ->
  (base + (11 + Z.of_nat count)) # UChar |-> 0 **
    event_storage_without_field named base
      (event_wait_table_init_prefix image count) (event_table_field (Z.of_nat count)) |--
  event_storage_rep named base (event_wait_table_init_prefix image (S count)).
Proof.
  intros named base image count Hcount; cbn [event_wait_table_init_prefix].
  rewrite <- event_table_cell_eq by lia.
  apply event_storage_merge_updated_field; apply event_table_field_in_fields.
Qed.

Definition event_payload_init_image (named : bool)
  (kind count pointer name : Z) (image : EventStorage) : EventStorage :=
  let initialized := event_write
    (event_write (event_write image EventTypeField (Some kind)) EventCntField (Some count))
    EventPtrField (Some pointer) in
  if named then event_write initialized EventNameField (Some name) else initialized.

Definition event_create_image (named : bool)
  (kind count pointer name : Z) (image : EventStorage) : EventStorage :=
  event_wait_list_init_image (event_payload_init_image named kind count pointer name image).

Definition event_clear_wait_row (image : EventStorage)
  (row row_value bit_x : Z) : EventStorage :=
  event_write image (event_table_field row)
    (Some (Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8))).

Definition event_clear_waiter (image : EventStorage)
  (row row_value group_value bit_x bit_y : Z) : EventStorage :=
  let cleared := Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8) in
  let row_image := event_clear_wait_row image row row_value bit_x in
  if Z.eqb cleared 0
  then event_write row_image EventGrpField
    (Some (Z.land group_value (unsigned_last_nbits (Z.lnot bit_y) 8)))
  else row_image.

(** Read the row, write its cleared value, and read/write the group only
    on the zero-row branch, as in Remove/RemoveMulti.  None denotes an
    unavailable input value, not an error check added to the C helper.
    The caller separately establishes the row bound and cell ownership. *)
Definition event_clear_waiter_from_image (image : EventStorage)
  (row bit_x bit_y : Z) : option EventStorage :=
  match image (event_table_field row) with
  | None => None
  | Some row_value =>
      let row_image := event_clear_wait_row image row row_value bit_x in
      if Z.eqb (Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8)) 0
      then match image EventGrpField with
           | None => None
           | Some group_value => Some (event_write row_image EventGrpField
               (Some (Z.land group_value (unsigned_last_nbits (Z.lnot bit_y) 8))))
           end
      else Some row_image
  end.

Lemma event_clear_waiter_from_image_eq : forall image row row_value group_value bit_x bit_y,
  image (event_table_field row) = Some row_value ->
  image EventGrpField = Some group_value ->
  event_clear_waiter_from_image image row bit_x bit_y =
    Some (event_clear_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros; unfold event_clear_waiter_from_image, event_clear_waiter.
  rewrite H; destruct (Z.eqb _ 0); [rewrite H0|]; reflexivity.
Qed.

Lemma event_clear_wait_row_merge : forall named base image row row_value bit_x,
  0 <= row < 8 ->
  (base + (11 + row)) # UChar |-> Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8) **
    event_storage_without_field named base image (event_table_field row) |--
  event_storage_rep named base (event_clear_wait_row image row row_value bit_x).
Proof.
  intros; rewrite <- event_table_cell_eq by assumption.
  apply event_storage_merge_updated_field; apply event_table_field_in_fields.
Qed.

Lemma event_clear_waiter_merge_empty_group :
  forall named base image row row_value group_value bit_x bit_y,
    Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8) = 0 ->
    (base + 10) # UChar |-> Z.land group_value (unsigned_last_nbits (Z.lnot bit_y) 8) **
      event_storage_without_field named base
        (event_clear_wait_row image row row_value bit_x) EventGrpField |--
    event_storage_rep named base
      (event_clear_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros named base image row row_value group_value bit_x bit_y Hempty.
  unfold event_clear_waiter; rewrite Hempty; simpl.
  apply (event_storage_merge_updated_field named base
    (event_clear_wait_row image row row_value bit_x) EventGrpField
    (Some (Z.land group_value (unsigned_last_nbits (Z.lnot bit_y) 8)))).
  unfold event_fields; simpl; tauto.
Qed.

Lemma event_clear_waiter_nonempty_group_eq : forall image row row_value group_value bit_x bit_y,
  Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8) <> 0 ->
  event_clear_waiter image row row_value group_value bit_x bit_y =
    event_clear_wait_row image row row_value bit_x.
Proof.
  intros; unfold event_clear_waiter; destruct (Z.eqb _ 0) eqn:E;
    [apply Z.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma event_clear_waiter_unwritten_field_eq : forall image row row_value group_value bit_x bit_y field,
  field <> event_table_field row -> field <> EventGrpField ->
  event_clear_waiter image row row_value group_value bit_x bit_y field = image field.
Proof.
  intros; unfold event_clear_waiter; destruct (Z.eqb _ 0).
  - unfold event_write; rewrite field_update_other by assumption.
    unfold event_clear_wait_row, event_write; apply field_update_other; assumption.
  - unfold event_clear_wait_row, event_write; apply field_update_other; assumption.
Qed.

Lemma event_clear_waiter_table_field_eq : forall image row row_value group_value bit_x bit_y other,
  0 <= row < 8 -> 0 <= other < 8 ->
  event_clear_waiter image row row_value group_value bit_x bit_y (event_table_field other) =
    if Z.eqb other row
    then Some (Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8))
    else image (event_table_field other).
Proof.
  intros image row row_value group_value bit_x bit_y other Hrow Hother.
  unfold event_clear_waiter; destruct (Z.eqb _ 0);
    [unfold event_write; rewrite field_update_other by apply event_table_field_not_group|];
    unfold event_clear_wait_row, event_write;
    destruct (Z.eqb other row) eqn:E.
  - apply Z.eqb_eq in E; subst other; apply field_update_same.
  - apply Z.eqb_neq in E; apply field_update_other; intro Heq; apply E;
      eapply event_table_field_injective; eauto.
  - apply Z.eqb_eq in E; subst other; apply field_update_same.
  - apply Z.eqb_neq in E; apply field_update_other; intro Heq; apply E;
      eapply event_table_field_injective; eauto.
Qed.

Lemma event_clear_waiter_group_field_eq : forall image row row_value group_value bit_x bit_y,
  image EventGrpField = Some group_value ->
  event_clear_waiter image row row_value group_value bit_x bit_y EventGrpField =
    Some (if Z.eqb (Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8)) 0
      then Z.land group_value (unsigned_last_nbits (Z.lnot bit_y) 8) else group_value).
Proof.
  intros; unfold event_clear_waiter; destruct (Z.eqb _ 0).
  - unfold event_write; apply field_update_same.
  - unfold event_clear_wait_row, event_write; rewrite field_update_other;
      [exact H|intro Heq; apply (event_table_field_not_group row); symmetry; exact Heq].
Qed.

(** OS_EventTaskWait and WaitMulti write the selected row before the
    group byte.  TCB EventPtr/MultiPtr stores are owned by the Task layer. *)
Definition event_mark_wait_row (image : EventStorage)
  (row row_value bit_x : Z) : EventStorage :=
  event_write image (event_table_field row) (Some (Z.lor row_value bit_x)).

Definition event_mark_waiter (image : EventStorage)
  (row row_value group_value bit_x bit_y : Z) : EventStorage :=
  event_write (event_mark_wait_row image row row_value bit_x)
    EventGrpField (Some (Z.lor group_value bit_y)).

Lemma event_mark_wait_row_merge : forall named base image row row_value bit_x,
  0 <= row < 8 ->
  (base + (11 + row)) # UChar |-> Z.lor row_value bit_x **
    event_storage_without_field named base image (event_table_field row) |--
  event_storage_rep named base (event_mark_wait_row image row row_value bit_x).
Proof.
  intros; rewrite <- event_table_cell_eq by assumption.
  apply event_storage_merge_updated_field; apply event_table_field_in_fields.
Qed.

Lemma event_mark_waiter_merge_group : forall named base image row row_value group_value bit_x bit_y,
  (base + 10) # UChar |-> Z.lor group_value bit_y **
    event_storage_without_field named base
      (event_mark_wait_row image row row_value bit_x) EventGrpField |--
  event_storage_rep named base
    (event_mark_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros; apply (event_storage_merge_updated_field named base
    (event_mark_wait_row image row row_value bit_x) EventGrpField (Some (Z.lor group_value bit_y))).
  unfold event_fields; simpl; tauto.
Qed.

Lemma event_mark_wait_row_group_field_eq : forall image row row_value bit_x,
  event_mark_wait_row image row row_value bit_x EventGrpField = image EventGrpField.
Proof.
  intros; unfold event_mark_wait_row, event_write; apply field_update_other.
  intro Heq; apply (event_table_field_not_group row); symmetry; exact Heq.
Qed.

Definition event_mark_waiter_from_image (image : EventStorage)
  (row bit_x bit_y : Z) : option EventStorage :=
  match image (event_table_field row) with
  | None => None
  | Some row_value =>
      let row_image := event_mark_wait_row image row row_value bit_x in
      match row_image EventGrpField with
      | None => None
      | Some group_value => Some (event_write row_image EventGrpField
          (Some (Z.lor group_value bit_y)))
      end
  end.

Lemma event_mark_waiter_from_image_eq : forall image row row_value group_value bit_x bit_y,
  image (event_table_field row) = Some row_value ->
  image EventGrpField = Some group_value ->
  event_mark_waiter_from_image image row bit_x bit_y =
    Some (event_mark_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros; unfold event_mark_waiter_from_image.
  rewrite H, event_mark_wait_row_group_field_eq, H0; reflexivity.
Qed.

Lemma event_mark_waiter_unwritten_field_eq : forall image row row_value group_value bit_x bit_y field,
  field <> event_table_field row -> field <> EventGrpField ->
  event_mark_waiter image row row_value group_value bit_x bit_y field = image field.
Proof.
  intros; unfold event_mark_waiter, event_mark_wait_row, event_write.
  rewrite !field_update_other by assumption; reflexivity.
Qed.

Lemma event_mark_waiter_table_field_eq : forall image row row_value group_value bit_x bit_y other,
  0 <= row < 8 -> 0 <= other < 8 ->
  event_mark_waiter image row row_value group_value bit_x bit_y (event_table_field other) =
    if Z.eqb other row then Some (Z.lor row_value bit_x) else image (event_table_field other).
Proof.
  intros image row row_value group_value bit_x bit_y other Hrow Hother.
  unfold event_mark_waiter, event_write.
  rewrite field_update_other by apply event_table_field_not_group.
  unfold event_mark_wait_row, event_write; destruct (Z.eqb other row) eqn:E.
  - apply Z.eqb_eq in E; subst other; apply field_update_same.
  - apply Z.eqb_neq in E; apply field_update_other; intro Heq; apply E.
    eapply event_table_field_injective; eauto.
Qed.

Lemma event_mark_waiter_group_field_eq : forall image row row_value group_value bit_x bit_y,
  event_mark_waiter image row row_value group_value bit_x bit_y EventGrpField =
    Some (Z.lor group_value bit_y).
Proof. intros; unfold event_mark_waiter, event_write; apply field_update_same. Qed.

Lemma event_private_set_mutex_pcp_preserves_partition : forall sg events eid allocation pcp,
  event_pool_partition sg events ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_pool_partition sg (event_private_set_mutex_pcp events eid allocation pcp).
Proof.
  intros sg events eid allocation pcp [Hpartition Hdisjoint] Hget.
  assert (Hslots : event_allocated_slots (event_private_set_mutex_pcp events eid allocation pcp) =
    kernel_map_set (event_allocated_slots events) eid
      (Some (inr {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
                    eventPrivateGeneration := allocation.(eventPrivateGeneration);
                    eventPrivateQueue := allocation.(eventPrivateQueue);
                    eventPrivateMutexPCP := pcp;
                    eventPrivateStorage := allocation.(eventPrivateStorage) |}))).
  { apply functional_extensionality; intro slot; unfold event_allocated_slots,
      event_private_set_mutex_pcp, event_set_lifecycle; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec slot eid); reflexivity. }
  split.
  - rewrite Hslots; eapply kernel_pool_replace_preserves_partition;
      [exact Hpartition|apply event_allocated_slots_private; exact Hget].
  - intros slot other Hother; simpl in Hother |- *; unfold kernel_map_set in Hother.
    destruct (Z.eq_dec slot eid) as [->|Hne]; eapply Hdisjoint; eauto.
Qed.

Lemma event_private_set_mutex_pcp_preserves_free_storage : forall sg events eid allocation pcp,
  event_free_storage_valid sg events ->
  event_free_storage_valid sg (event_private_set_mutex_pcp events eid allocation pcp).
Proof. intros; exact H. Qed.

Lemma event_private_set_mutex_pcp_preserves_identity : forall events eid allocation pcp,
  event_identity_valid events ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_identity_valid (event_private_set_mutex_pcp events eid allocation pcp).
Proof.
  intros events eid allocation pcp Hvalid Hget.
  eapply event_identity_valid_from_submap;
    [exact Hvalid|apply Nat.le_refl|apply Nat.le_refl| |].
  - intros slot generation Hslot; unfold event_slot_generation, event_allocated_slots,
      event_private_set_mutex_pcp, event_set_lifecycle in Hslot |- *; simpl in Hslot.
    unfold kernel_map_set in Hslot; destruct (Z.eq_dec slot eid) as [->|Hne];
      [rewrite Hget|]; exact Hslot.
  - intros slot invocation Hslot; unfold event_private_invocation,
      event_private_set_mutex_pcp, event_set_lifecycle in Hslot |- *; simpl in Hslot.
    unfold kernel_map_set in Hslot; destruct (Z.eq_dec slot eid) as [->|Hne];
      [rewrite Hget|]; exact Hslot.
Qed.

Lemma event_private_set_mutex_pcp_frames_other_invocation :
  forall events eid allocation pcp observer,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) <> observer ->
  event_creation_frame observer events (event_private_set_mutex_pcp events eid allocation pcp).
Proof.
  intros events eid allocation pcp observer Hget Hforeign.
  eapply event_creation_view_update_foreign with (eid := eid).
  - intros; simpl; apply kernel_map_set_other; assumption.
  - intros other Hother; congruence.
  - intros other Hother; simpl in Hother; rewrite kernel_map_set_same in Hother.
    injection Hother as Hother; subst other; exact Hforeign.
Qed.

Lemma event_private_write_mutex_pcp_eq : forall events eid allocation field stored,
  (event_private_write events eid allocation field stored).(eventLifecycle).(eventPrivate) eid =
  Some {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
          eventPrivateGeneration := allocation.(eventPrivateGeneration);
          eventPrivateQueue := allocation.(eventPrivateQueue);
          eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
          eventPrivateStorage := event_write allocation.(eventPrivateStorage) field stored |}.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma event_publish_detach_mutex_eq : forall sg events eid rest image pcp node,
  event_publish (event_detach_mutex_head sg events eid rest image pcp) eid node =
  event_publish (event_detach_head events eid rest image) eid node.
Proof.
  intros; unfold event_publish, event_detach_mutex_head, event_private_set_mutex_pcp,
    event_detach_head, event_set_lifecycle; simpl.
  f_equal; f_equal; apply functional_extensionality; intro other.
  unfold kernel_map_set; destruct (Z.eq_dec other eid); reflexivity.
Qed.

Lemma event_mutex_lease_view_private_write_eq : forall events eid allocation field stored,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_mutex_lease_view (event_private_write events eid allocation field stored) =
    event_mutex_lease_view events.
Proof.
  intros events eid allocation field stored Hget; apply functional_extensionality; intro other.
  unfold event_mutex_lease_view, event_private_write, event_set_lifecycle; simpl.
  unfold kernel_map_set; destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hget|]; reflexivity.
Qed.

Lemma event_mutex_lease_view_detach_head_eq : forall events eid rest image,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  event_mutex_lease_view (event_detach_head events eid rest image) = event_mutex_lease_view events.
Proof.
  intros events eid rest image Hnone; apply functional_extensionality; intro other.
  unfold event_mutex_lease_view, event_detach_head; simpl; unfold kernel_map_set.
  destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hnone|]; reflexivity.
Qed.

Lemma event_mutex_lease_view_publish_eq : forall events eid allocation node,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateMutexPCP) = None ->
  event_mutex_lease_view (event_publish events eid node) = event_mutex_lease_view events.
Proof.
  intros events eid allocation node Hget Hnone; apply functional_extensionality; intro other.
  unfold event_mutex_lease_view, event_publish; simpl; unfold kernel_map_set.
  destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hget, Hnone|]; reflexivity.
Qed.

Lemma event_mutex_lease_view_recycle_eq : forall sg events eid image,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  event_mutex_lease_view (event_recycle sg events eid image) = event_mutex_lease_view events.
Proof.
  intros sg events eid image Hnone; apply functional_extensionality; intro other.
  unfold event_mutex_lease_view, event_recycle; simpl; unfold kernel_map_set.
  destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hnone|]; reflexivity.
Qed.
