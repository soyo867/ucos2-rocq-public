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
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.field_storage.

Import UCOS2_C_Rules EventStateDef EventFieldStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** The public helper contract owns only the nine writable bitmap bytes.
    It neither reads their initial values nor owns the initialized payload,
    padding, pool, task or scheduler resources.  The two addresses are the
    actual C field addresses, so this focused contract needs no ABI premise. *)
Definition event_wait_list_init_pre (group table : addr) : Assertion :=
  group # UChar |->_ ** UCharArray.undef_full table 8.

Definition event_wait_list_init_post (group table : addr) : Assertion :=
  group # UChar |-> 0 ** UCharArray.full table 8 (repeat 0 8).

(** The processed rows are exactly zero, and every unprocessed row still
    has writable ownership.  This uses QCP's byte-array representation. *)
Definition event_wait_list_init_table_prefix (table count : Z) : Assertion :=
  UCharArray.full table count (repeat 0 (Z.to_nat count)) **
  UCharArray.undef_seg table count 8.

Definition event_wait_list_init_row_frame (table count : Z) : Assertion :=
  UCharArray.full table count (repeat 0 (Z.to_nat count)) **
  UCharArray.undef_seg table (count + 1) 8.

Lemma event_wait_list_init_pre_split_group : forall group table,
  event_wait_list_init_pre group table |--
  group # UChar |->_ ** event_wait_list_init_table_prefix table 0.
Proof.
  intros; unfold event_wait_list_init_pre, event_wait_list_init_table_prefix.
  change (Z.to_nat 0) with 0%nat; simpl repeat.
  rewrite UCharArray.full_empty.
  change (UCharArray.undef_full table 8) with (UCharArray.undef_seg table 0 8).
  entailer!.
Qed.

Lemma event_wait_list_init_table_prefix_split_row : forall table count,
  0 <= count < 8 ->
  event_wait_list_init_table_prefix table count |--
  (table + count) # UChar |->_ ** event_wait_list_init_row_frame table count.
Proof.
  intros table count Hcount.
  unfold event_wait_list_init_table_prefix, event_wait_list_init_row_frame.
  rewrite UCharArray.undef_seg_unfold by lia.
  unfold StoreUCharAsElement.undefstoreA; change (sizeof(UCHAR)) with 1.
  replace (table + count * 1) with (table + count) by lia; entailer!.
Qed.

Lemma event_wait_list_init_table_prefix_merge_row : forall table count,
  0 <= count < 8 ->
  (table + count) # UChar |-> 0 ** event_wait_list_init_row_frame table count |--
  event_wait_list_init_table_prefix table (count + 1).
Proof.
  intros table count Hcount.
  unfold event_wait_list_init_row_frame, event_wait_list_init_table_prefix.
  assert (Hrepeat : repeat 0 (Z.to_nat (count + 1)) =
    repeat 0 (Z.to_nat count) ++ [0]).
  { replace (Z.to_nat (count + 1)) with (Z.to_nat count + 1)%nat by lia.
    apply repeat_app. }
  rewrite Hrepeat.
  assert (Hcell : (table + count) # UChar |-> 0 |--
    UCharArray.full (table + count) 1 [0]).
  { rewrite UCharArray.full_unfold, UCharArray.seg_empty.
    unfold StoreUCharAsElement.storeA, StoreUCharAsElement.sizeA;
      change (sizeof(UCHAR)) with 1.
    replace (table + count + 0 * 1) with (table + count) by lia.
    entailer!. }
  sep_apply_l_atomic Hcell.
  pose proof (UCharArray.full_merge_to_full table count (count + 1)
    (repeat 0 (Z.to_nat count)) [0] ltac:(lia)) as Hmerge.
  unfold StoreUCharAsElement.sizeA in Hmerge; change (sizeof(UCHAR)) with 1 in Hmerge.
  replace (table + count * 1) with (table + count) in Hmerge by lia.
  replace (count + 1 - count) with 1 in Hmerge by lia.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

(** Only the non-written fields of this function. Each cell is the
    authoritative event_pool cell; all padding bytes and the optional
    OSEventName pointer retain their original values. *)
Definition event_wait_list_init_storage_frame (named : bool) (base : addr)
  (image : EventStorage) : Assertion :=
  event_cell base EventTypeField (image EventTypeField) **
  event_cell base EventPadding1 (image EventPadding1) **
  event_cell base EventPadding2 (image EventPadding2) **
  event_cell base EventPadding3 (image EventPadding3) **
  event_cell base EventPtrField (image EventPtrField) **
  event_cell base EventCntField (image EventCntField) **
  event_cell base EventPadding19 (image EventPadding19) **
  (if named then event_cell base EventNameField (image EventNameField) else emp).

Lemma event_wait_list_init_storage_split : forall named base image,
  event_storage_rep named base image |--
  event_wait_list_init_pre (base + 10) (base + 11) **
  event_wait_list_init_storage_frame named base image.
Proof.
  intros named base image.
  assert (Hforget : forall field,
    event_cell base field (image field) |-- event_cell base field None).
  { intro field; destruct field; cbn [event_cell];
      match goal with |- context [image ?field] => destruct (image field) end;
      first [apply store_uchar_undef_store_uchar |
             apply store_ptr_undef_store_ptr |
             apply store_ushort_undef_store_ushort | entailer!]. }
  destruct named; unfold event_wait_list_init_pre, event_wait_list_init_storage_frame,
    event_storage_rep, event_fields; simpl app.
  all: repeat rewrite store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  all: rewrite store_fields_nil.
  all: sep_apply_l_atomic (Hforget EventGrpField).
  all: sep_apply_l_atomic (Hforget EventTbl0).
  all: sep_apply_l_atomic (Hforget EventTbl1).
  all: sep_apply_l_atomic (Hforget EventTbl2).
  all: sep_apply_l_atomic (Hforget EventTbl3).
  all: sep_apply_l_atomic (Hforget EventTbl4).
  all: sep_apply_l_atomic (Hforget EventTbl5).
  all: sep_apply_l_atomic (Hforget EventTbl6).
  all: sep_apply_l_atomic (Hforget EventTbl7).
  all: change (UCharArray.undef_full (base + 11) 8)
    with (UCharArray.undef_seg (base + 11) 0 8).
  all: do 8 (rewrite UCharArray.undef_seg_unfold by lia).
  all: rewrite UCharArray.undef_seg_empty.
  all: unfold event_cell, event_field_offset, StoreUCharAsElement.undefstoreA;
    change (sizeof(UCHAR)) with 1.
  all: repeat match goal with
  | |- context [?start + 11 + ?row * 1] =>
      let offset := eval compute in (11 + row) in
      replace (start + 11 + row * 1) with (start + offset) by lia
  end.
  all: entailer!.
Qed.

Lemma event_wait_list_init_storage_merge : forall named base image,
  event_wait_list_init_post (base + 10) (base + 11) **
  event_wait_list_init_storage_frame named base image |--
  event_storage_rep named base (event_wait_list_init_image image).
Proof.
  intros named base image.
  assert (Hfields : forall field,
    event_wait_list_init_image image field =
    match field with
    | EventGrpField | EventTbl0 | EventTbl1 | EventTbl2 | EventTbl3
    | EventTbl4 | EventTbl5 | EventTbl6 | EventTbl7 => Some 0
    | _ => image field
    end).
  { intro field; destruct field; reflexivity. }
  destruct named; unfold event_wait_list_init_post, event_wait_list_init_storage_frame,
    event_storage_rep, event_fields; simpl app.
  all: repeat rewrite store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  all: rewrite store_fields_nil.
  all: rewrite !Hfields.
  all: cbn [repeat].
  all: rewrite UCharArray.full_unfold.
  all: repeat rewrite UCharArray.seg_unfold.
  all: rewrite UCharArray.seg_empty.
  all: unfold event_cell, event_field_offset, StoreUCharAsElement.storeA;
    change (sizeof(UCHAR)) with 1.
  all: repeat match goal with
  | |- context [?start + 11 + ?row * 1] =>
      let offset := eval compute in (11 + row) in
      replace (start + 11 + row * 1) with (start + offset) by lia
  end.
  all: entailer!.
Qed.

(** The full-image consequence uses the existing module-owned C-layout
    premise, not a per-helper axiom.  This is a privately owned ECB image,
    not a claim that the whole running kernel invariant is restored. *)
Lemma event_wait_list_init_storage_layout_consequence : forall sg eid image,
  event_object_layout_prop sg eid ->
  event_wait_list_init_post
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl")) **
  event_wait_list_init_storage_frame sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) image |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) (event_wait_list_init_image image).
Proof.
  intros sg eid image [_ [Hgroup Htable]].
  unfold OSEventGrp_off, OSEventTbl_off in Hgroup, Htable.
  rewrite Hgroup, Htable, event_addr_shared_pool_binding.
  apply event_wait_list_init_storage_merge.
Qed.

Lemma event_wait_list_init_post_merge_table : forall group table,
  group # UChar |-> 0 ** event_wait_list_init_table_prefix table 8 |--
  event_wait_list_init_post group table.
Proof.
  intros; unfold event_wait_list_init_table_prefix, event_wait_list_init_post.
  rewrite UCharArray.undef_seg_empty; entailer!.
Qed.

(** The source-order transformer is owned by event_pool.  These observers
    connect the exact array postcondition to that existing EventStorage image. *)
Lemma event_wait_list_init_image_observations : forall image,
  event_wait_list_init_image image EventGrpField = Some 0 /\
  (forall row, 0 <= row < 8 ->
    event_wait_list_init_image image (event_table_field row) = Some 0) /\
  (forall field, field <> EventGrpField ->
    (forall row, 0 <= row < 8 -> field <> event_table_field row) ->
    event_wait_list_init_image image field = image field).
Proof.
  intros image; split; [apply event_wait_list_init_group|].
  split; [apply event_wait_list_init_table|apply event_wait_list_init_frame].
Qed.
