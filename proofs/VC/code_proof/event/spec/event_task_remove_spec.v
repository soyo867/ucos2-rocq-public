Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event.

Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** Exact typed-byte observations.  The mask complement is converted to
    OS_PRIO before the AND, as in the selected unsigned-byte C profile. *)
Definition event_task_remove_cleared (value mask : Z) : Z :=
  Z.land value (unsigned_last_nbits (Z.lnot mask) 8).

Definition event_task_remove_group (row_value group_value bit_x bit_y : Z) : Z :=
  if Z.eqb (event_task_remove_cleared row_value bit_x) 0
  then event_task_remove_cleared group_value bit_y else group_value.

(** The caller supplies exclusive ownership of the accessed cells.  This
    internal helper neither acquires a lock nor restores a stable kernel
    invariant.  In particular no pending status, delay or message premise is
    required: OS_EventTaskRdy has already written those fields at this call.
    Only one bitmap row is owned here; all other cells and arbitrary disjoint
    resources are preserved by the ordinary separation-logic frame rule. *)
Definition event_task_remove_pre
  (tcb group table row bit_x bit_y row_value group_value : Z) : Assertion :=
  “ (0 <= row /\ row < 8) ” &&
  (tcb_field_address tcb TCBY # UChar |-> row **
   tcb_field_address tcb TCBBitX # UChar |-> bit_x **
   tcb_field_address tcb TCBBitY # UChar |-> bit_y **
   tcb_field_address tcb TCBEventPtr # Ptr |->_ **
   group # UChar |-> group_value **
   (table + row) # UChar |-> row_value).

Definition event_task_remove_post
  (tcb group table row bit_x bit_y row_value group_value : Z) : Assertion :=
  “ (0 <= row /\ row < 8) ” &&
  (tcb_field_address tcb TCBY # UChar |-> row **
   tcb_field_address tcb TCBBitX # UChar |-> bit_x **
   tcb_field_address tcb TCBBitY # UChar |-> bit_y **
   tcb_field_address tcb TCBEventPtr # Ptr |-> 0 **
   group # UChar |-> event_task_remove_group row_value group_value bit_x bit_y **
   (table + row) # UChar |-> event_task_remove_cleared row_value bit_x).

(** These residuals use the existing finite-field storage interface.  They
    retain every nonaccessed field, including optional padding contents. *)
Definition event_task_remove_tcb_frame (base : addr) (image : TCBCommonImage)
  : Assertion :=
  tcb64_fields_rep base
    (remove TCBField_eq_dec TCBEventPtr
      (remove TCBField_eq_dec TCBBitY
        (remove TCBField_eq_dec TCBBitX
          (remove TCBField_eq_dec TCBY tcb_fields)))) image.

Definition event_task_remove_ecb_frame (named : bool) (base : addr) (image : EventStorage)
  (row : Z) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec EventGrpField
      (remove EventField_eq_dec (event_table_field row) (event_fields named))) image.

Lemma event_task_remove_tcb_split : forall base image row bit_x bit_y,
  image TCBY = Some row -> image TCBBitX = Some bit_x ->
  image TCBBitY = Some bit_y ->
  tcb64_storage_rep base image |--
  tcb_field_address base TCBY # UChar |-> row **
  tcb_field_address base TCBBitX # UChar |-> bit_x **
  tcb_field_address base TCBBitY # UChar |-> bit_y **
  tcb_field_address base TCBEventPtr # Ptr |->_ **
  event_task_remove_tcb_frame base image.
Proof.
  intros base image row bit_x bit_y Hrow Hx Hy.
  assert (Hptr : tcb_cell base TCBEventPtr (image TCBEventPtr) |--
    tcb_field_address base TCBEventPtr # Ptr |->_).
  { unfold tcb_cell; destruct (image TCBEventPtr);
      [apply store_ptr_undef_store_ptr|entailer!]. }
  set (fields_y := remove TCBField_eq_dec TCBY tcb_fields).
  set (fields_x := remove TCBField_eq_dec TCBBitX fields_y).
  set (fields_bits := remove TCBField_eq_dec TCBBitY fields_x).
  assert (Hnd_y : NoDup fields_y) by
    (unfold fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  assert (Hnd_x : NoDup fields_x) by
    (unfold fields_x, fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  assert (Hnd_bits : NoDup fields_bits) by
    (unfold fields_bits, fields_x, fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  sep_apply_l_atomic (tcb64_storage_split base image TCBY).
  unfold tcb64_storage_without; fold fields_y.
  sep_apply_l_atomic (tcb64_fields_rep_split fields_y base image TCBBitX
    Hnd_y ltac:(unfold fields_y, tcb_fields; vm_compute; intuition congruence)).
  fold fields_x.
  sep_apply_l_atomic (tcb64_fields_rep_split fields_x base image TCBBitY
    Hnd_x ltac:(unfold fields_x, fields_y, tcb_fields; vm_compute; intuition congruence)).
  fold fields_bits.
  sep_apply_l_atomic (tcb64_fields_rep_split fields_bits base image TCBEventPtr
    Hnd_bits ltac:(unfold fields_bits, fields_x, fields_y, tcb_fields; vm_compute; intuition congruence)).
  sep_apply_l_atomic Hptr.
  unfold event_task_remove_tcb_frame; fold fields_y; fold fields_x; fold fields_bits.
  rewrite Hrow, Hx, Hy; cbn [tcb_cell]; entailer!.
Qed.

Lemma event_task_remove_tcb_merge_updated : forall base image row bit_x bit_y,
  image TCBY = Some row -> image TCBBitX = Some bit_x ->
  image TCBBitY = Some bit_y ->
  tcb_field_address base TCBY # UChar |-> row **
  tcb_field_address base TCBBitX # UChar |-> bit_x **
  tcb_field_address base TCBBitY # UChar |-> bit_y **
  tcb_field_address base TCBEventPtr # Ptr |-> 0 **
  event_task_remove_tcb_frame base image |--
  tcb64_storage_rep base (tcb_write image TCBEventPtr (Some 0)).
Proof.
  intros base image row bit_x bit_y Hrow Hx Hy.
  set (fields_y := remove TCBField_eq_dec TCBY tcb_fields).
  set (fields_x := remove TCBField_eq_dec TCBBitX fields_y).
  set (fields_bits := remove TCBField_eq_dec TCBBitY fields_x).
  assert (Hnd_y : NoDup fields_y) by
    (unfold fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  assert (Hnd_x : NoDup fields_x) by
    (unfold fields_x, fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  assert (Hnd_bits : NoDup fields_bits) by
    (unfold fields_bits, fields_x, fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  unfold event_task_remove_tcb_frame; fold fields_y; fold fields_x; fold fields_bits.
  pose proof (tcb64_fields_rep_merge_updated fields_bits base image TCBEventPtr (Some 0)
    Hnd_bits ltac:(unfold fields_bits, fields_x, fields_y, tcb_fields; vm_compute; intuition congruence)) as Hpointer.
  cbn [tcb_cell] in Hpointer; sep_apply_l_atomic Hpointer.
  pose proof (tcb64_fields_rep_merge fields_x base (tcb_write image TCBEventPtr (Some 0))
    TCBBitY Hnd_x ltac:(unfold fields_x, fields_y, tcb_fields; vm_compute; intuition congruence)) as Hmerge_y.
  rewrite tcb_write_frame in Hmerge_y by discriminate.
  rewrite Hy in Hmerge_y; cbn [tcb_cell] in Hmerge_y; fold fields_bits in Hmerge_y.
  sep_apply_l_atomic Hmerge_y.
  pose proof (tcb64_fields_rep_merge fields_y base (tcb_write image TCBEventPtr (Some 0))
    TCBBitX Hnd_y ltac:(unfold fields_y, tcb_fields; vm_compute; intuition congruence)) as Hmerge_x.
  rewrite tcb_write_frame in Hmerge_x by discriminate.
  rewrite Hx in Hmerge_x; cbn [tcb_cell] in Hmerge_x; fold fields_x in Hmerge_x.
  sep_apply_l_atomic Hmerge_x.
  pose proof (tcb64_storage_merge base (tcb_write image TCBEventPtr (Some 0)) TCBY) as Hmerge_row.
  rewrite tcb_write_frame in Hmerge_row by discriminate.
  rewrite Hrow in Hmerge_row; cbn [tcb_cell] in Hmerge_row.
  unfold tcb64_storage_without in Hmerge_row; fold fields_y in Hmerge_row.
  sep_apply_l_atomic Hmerge_row; entailer!.
Qed.

Lemma event_task_remove_ecb_split : forall named base image row row_value group_value,
  0 <= row < 8 -> image (event_table_field row) = Some row_value ->
  image EventGrpField = Some group_value ->
  event_storage_rep named base image |--
  (base + 10) # UChar |-> group_value **
  (base + 11 + row) # UChar |-> row_value **
  event_task_remove_ecb_frame named base image row.
Proof.
  intros named base image row row_value group_value Hrow Hvalue Hgroup.
  assert (Hin : In EventGrpField
    (remove EventField_eq_dec (event_table_field row) (event_fields named))).
  { apply in_in_remove; [intro Heq; apply (event_table_field_not_group row); symmetry; exact Heq|].
    destruct named; unfold event_fields; simpl; tauto. }
  assert (Hnd : NoDup
    (remove EventField_eq_dec (event_table_field row) (event_fields named))).
  { destruct named, (event_table_field row); vm_compute;
      repeat constructor; simpl; intuition discriminate. }
  sep_apply_l_atomic (event_storage_split_field named base image
    (event_table_field row) (event_table_field_in_fields named row)).
  unfold event_storage_without_field.
  sep_apply_l_atomic (EventFieldStorage.store_fields_split_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec (event_table_field row) (event_fields named))
    image EventGrpField Hnd Hin).
  rewrite Hvalue, Hgroup, event_table_cell_eq by exact Hrow.
  replace (base + (11 + row)) with (base + 11 + row) by lia.
  unfold event_task_remove_ecb_frame; cbn [event_cell event_field_offset]; entailer!.
Qed.

Lemma event_task_remove_ecb_frame_update_eq :
  forall named base image row row_value group_value bit_x bit_y,
  event_task_remove_ecb_frame named base
    (event_clear_waiter image row row_value group_value bit_x bit_y) row =
  event_task_remove_ecb_frame named base image row.
Proof.
  intros named base image row row_value group_value bit_x bit_y.
  assert (Hgroup : ~ In EventGrpField
    (remove EventField_eq_dec EventGrpField
      (remove EventField_eq_dec (event_table_field row) (event_fields named))))
    by apply remove_In.
  assert (Hrow : ~ In (event_table_field row)
    (remove EventField_eq_dec EventGrpField
      (remove EventField_eq_dec (event_table_field row) (event_fields named)))).
  { intro Hin; apply in_remove in Hin; destruct Hin as [Hin _].
    eapply remove_In; exact Hin. }
  unfold event_task_remove_ecb_frame, event_clear_waiter.
  destruct (Z.eqb _ 0); unfold event_clear_wait_row, event_write;
    rewrite !EventFieldStorage.store_fields_update_unlisted by assumption;
    reflexivity.
Qed.

Lemma event_task_remove_ecb_merge_updated :
  forall named base image row row_value group_value bit_x bit_y,
  0 <= row < 8 -> image EventGrpField = Some group_value ->
  (base + 10) # UChar |-> event_task_remove_group row_value group_value bit_x bit_y **
  (base + 11 + row) # UChar |-> event_task_remove_cleared row_value bit_x **
  event_task_remove_ecb_frame named base image row |--
  event_storage_rep named base
    (event_clear_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros named base image row row_value group_value bit_x bit_y Hrow Hgroup.
  set (updated := event_clear_waiter image row row_value group_value bit_x bit_y).
  assert (Hrowval : updated (event_table_field row) =
    Some (event_task_remove_cleared row_value bit_x)).
  { unfold updated, event_task_remove_cleared.
    rewrite event_clear_waiter_table_field_eq by exact Hrow.
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hgroupval : updated EventGrpField =
    Some (event_task_remove_group row_value group_value bit_x bit_y)).
  { unfold updated, event_task_remove_group, event_task_remove_cleared.
    apply event_clear_waiter_group_field_eq; exact Hgroup. }
  assert (Hin : In EventGrpField
    (remove EventField_eq_dec (event_table_field row) (event_fields named))).
  { apply in_in_remove; [intro Heq; apply (event_table_field_not_group row); symmetry; exact Heq|].
    destruct named; unfold event_fields; simpl; tauto. }
  assert (Hnd : NoDup
    (remove EventField_eq_dec (event_table_field row) (event_fields named))).
  { destruct named, (event_table_field row); vm_compute;
      repeat constructor; simpl; intuition discriminate. }
  rewrite <- (event_task_remove_ecb_frame_update_eq named base image row
    row_value group_value bit_x bit_y).
  change (event_task_remove_ecb_frame named base
    (event_clear_waiter image row row_value group_value bit_x bit_y) row)
    with (event_task_remove_ecb_frame named base updated row).
  pose proof (EventFieldStorage.store_fields_merge_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec (event_table_field row) (event_fields named))
    updated EventGrpField Hnd Hin) as Hmerge_group.
  rewrite Hgroupval in Hmerge_group; cbn [event_cell event_field_offset] in Hmerge_group.
  unfold event_task_remove_ecb_frame; sep_apply_l_atomic Hmerge_group.
  pose proof (event_storage_merge_field named base updated
    (event_table_field row) (event_table_field_in_fields named row)) as Hmerge_row.
  rewrite Hrowval, event_table_cell_eq in Hmerge_row by exact Hrow.
  replace (base + (11 + row)) with (base + 11 + row) in Hmerge_row by lia.
  unfold event_storage_without_field in Hmerge_row.
  sep_apply_l_atomic Hmerge_row; entailer!.
Qed.

(** The numeric ECB interface is kept separate from its C layout bridge.
    No assumption relates arbitrary symbolic C field addresses to offsets. *)
Lemma event_task_remove_storage_split :
  forall named tcb base task_image image row bit_x bit_y row_value group_value,
  0 <= row < 8 ->
  task_image TCBY = Some row -> task_image TCBBitX = Some bit_x ->
  task_image TCBBitY = Some bit_y ->
  image (event_table_field row) = Some row_value ->
  image EventGrpField = Some group_value ->
  tcb64_storage_rep tcb task_image ** event_storage_rep named base image |--
  event_task_remove_pre tcb (base + 10) (base + 11)
    row bit_x bit_y row_value group_value **
  event_task_remove_tcb_frame tcb task_image **
  event_task_remove_ecb_frame named base image row.
Proof.
  intros named tcb base task_image image row bit_x bit_y row_value group_value
    Hrow Hy Hx Hby Hvalue Hgroup.
  sep_apply_l_atomic (event_task_remove_tcb_split tcb task_image row bit_x bit_y Hy Hx Hby).
  sep_apply_l_atomic (event_task_remove_ecb_split named base image row row_value group_value
    Hrow Hvalue Hgroup).
  unfold event_task_remove_pre; entailer!.
Qed.

Lemma event_task_remove_storage_merge_updated :
  forall named tcb base task_image image row bit_x bit_y row_value group_value,
  task_image TCBY = Some row -> task_image TCBBitX = Some bit_x ->
  task_image TCBBitY = Some bit_y -> image EventGrpField = Some group_value ->
  event_task_remove_post tcb (base + 10) (base + 11)
    row bit_x bit_y row_value group_value **
  event_task_remove_tcb_frame tcb task_image **
  event_task_remove_ecb_frame named base image row |--
  tcb64_storage_rep tcb (tcb_write task_image TCBEventPtr (Some 0)) **
  event_storage_rep named base
    (event_clear_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros named tcb base task_image image row bit_x bit_y row_value group_value
    Hy Hx Hby Hgroup.
  unfold event_task_remove_post; Intros.
  sep_apply_l_atomic (event_task_remove_tcb_merge_updated tcb task_image
    row bit_x bit_y Hy Hx Hby).
  sep_apply_l_atomic (event_task_remove_ecb_merge_updated named base image row
    row_value group_value bit_x bit_y H Hgroup).
  entailer!.
Qed.

Lemma event_task_remove_storage_layout_split :
  forall sg eid tcb task_image image row bit_x bit_y row_value group_value,
  event_object_layout_prop sg eid -> 0 <= row < 8 ->
  task_image TCBY = Some row -> task_image TCBBitX = Some bit_x ->
  task_image TCBBitY = Some bit_y ->
  image (event_table_field row) = Some row_value -> image EventGrpField = Some group_value ->
  tcb64_storage_rep tcb task_image **
    event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) image |--
  event_task_remove_pre tcb
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl"))
    row bit_x bit_y row_value group_value **
  event_task_remove_tcb_frame tcb task_image **
  event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) image row.
Proof.
  intros sg eid tcb task_image image row bit_x bit_y row_value group_value
    [_ [Hgroup Htable]] Hrow Hy Hx Hby Hvalue Hgroupval.
  unfold OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  rewrite Hgroup, Htable.
  apply event_task_remove_storage_split; assumption.
Qed.

Lemma event_task_remove_storage_layout_merge_updated :
  forall sg eid tcb task_image image row bit_x bit_y row_value group_value,
  event_object_layout_prop sg eid ->
  task_image TCBY = Some row -> task_image TCBBitX = Some bit_x ->
  task_image TCBBitY = Some bit_y -> image EventGrpField = Some group_value ->
  event_task_remove_post tcb
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl"))
    row bit_x bit_y row_value group_value **
  event_task_remove_tcb_frame tcb task_image **
  event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) image row |--
  tcb64_storage_rep tcb (tcb_write task_image TCBEventPtr (Some 0)) **
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_clear_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros sg eid tcb task_image image row bit_x bit_y row_value group_value
    [_ [Hgroup Htable]] Hy Hx Hby Hgroupval.
  unfold OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  rewrite Hgroup, Htable.
  apply event_task_remove_storage_merge_updated; assumption.
Qed.

(** The abstract consequence does not require a linked-wait phase and does
    not claim global-invariant preservation.  Priority/canonicality/lookup
    premises are exactly those consumed by the existing waiter-image lemma. *)
Lemma event_task_remove_abstract_storage_consequence :
  forall sg tasks eid e tid t tcb,
  event_object_layout_prop sg eid -> valid_stable_glob_vars sg ->
  task_priority_unique tasks -> event_waitList_canonical sg tasks e.(waitList) ->
  valid_task_prio sg t.(curPrio) -> tasks.(inUsedTaskStates) tid = Some t ->
  event_task_remove_post tcb
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl"))
    (t.(curPrio) / 8) (Z.shiftl 1 (t.(curPrio) mod 8))
    (Z.shiftl 1 (t.(curPrio) / 8))
    (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
    (encode_event_wait_grp e.(waitList) tasks) **
  event_task_remove_tcb_frame tcb (task_tcb64_image sg t) **
  event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks e)
    (t.(curPrio) / 8) |--
  tcb64_storage_rep tcb (task_tcb64_image sg (task_set_event_ptr t None)) **
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
Proof.
  intros sg tasks eid e tid t tcb Hlayout Hsg Hunique Hcanonical Hprio Hlookup.
  rewrite task_set_event_ptr_image_eq.
  change (encode_event_link sg None) with 0.
  rewrite (event_remove_waiter_image_eq sg tasks e tid t Hsg Hunique Hcanonical Hprio Hlookup).
  apply event_task_remove_storage_layout_merge_updated; try exact Hlayout; reflexivity.
Qed.

Lemma event_task_remove_image_operation_eq : forall image row bit_x bit_y row_value group_value,
  image (event_table_field row) = Some row_value -> image EventGrpField = Some group_value ->
  event_clear_waiter_from_image image row bit_x bit_y =
    Some (event_clear_waiter image row row_value group_value bit_x bit_y).
Proof. intros; apply event_clear_waiter_from_image_eq; assumption. Qed.
