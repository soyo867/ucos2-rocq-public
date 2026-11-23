Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_configured_storage.

Import ListNotations EventStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma remove_preserves_nodup__event_fields : forall (A : Type)
  (dec : forall x y : A, {x = y} + {x <> y}) x fields,
  NoDup fields -> NoDup (remove dec x fields).
Proof.
  intros A dec x fields Hnd; induction Hnd as [|head rest Hnot Hnd IH]; cbn.
  - constructor.
  - destruct (dec x head) as [Heq|Hne]; [exact IH|].
    constructor; [|exact IH].
    intro Hin; apply Hnot; apply in_remove in Hin; tauto.
Qed.

Lemma event_fields_remove_nodup : forall named field,
  NoDup (remove EventField_eq_dec field (event_fields named)).
Proof.
  intros named field. unfold event_fields.
  destruct named; apply remove_preserves_nodup__event_fields.
  all: repeat constructor; simpl; intuition discriminate.
Qed.

(** Configuration-parametric Event wait focus.  The old wait spec hard-coded
    [false] and 20 bytes; this interface carries the selected Event-name bit
    through the storage and leaves the optional name cell in the residual. *)
Definition event_task_wait_configured_rest (named : bool) (base : addr)
  (row : Z) (image : EventStorage) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec EventGrpField
      (remove EventField_eq_dec (event_table_field row) (event_fields named))) image.

Lemma event_task_wait_configured_split : forall named base image row row_value group_value,
  0 <= row < 8 -> image (event_table_field row) = Some row_value ->
  image EventGrpField = Some group_value ->
  event_storage_rep named base image |--
  (base + (11 + row)) # UChar |-> row_value **
  (base + 10) # UChar |-> group_value **
  event_task_wait_configured_rest named base row image.
Proof.
  intros named base image row row_value group_value Hrow Htable Hgroup.
  sep_apply_l_atomic (event_storage_split_field named base image
    (event_table_field row) (event_table_field_in_fields named row)).
  rewrite Htable, event_table_cell_eq by exact Hrow.
  unfold event_storage_without_field.
  sep_apply_l_atomic (EventFieldStorage.store_fields_split_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec (event_table_field row) (event_fields named)) image EventGrpField
    ltac:(apply event_fields_remove_nodup)
    ltac:(apply in_in_remove; [intro E; apply (event_table_field_not_group row); symmetry; exact E|]
      ; destruct named; cbn [event_fields]; repeat constructor; simpl; intuition discriminate)).
  rewrite Hgroup; unfold event_task_wait_configured_rest;
    cbn [event_cell event_field_offset]; entailer!.
Qed.

Lemma event_task_wait_configured_merge : forall named base image row row_value group_value bit_x bit_y,
  0 <= row < 8 ->
  (base + (11 + row)) # UChar |-> Z.lor row_value bit_x **
  (base + 10) # UChar |-> Z.lor group_value bit_y **
  event_task_wait_configured_rest named base row image |--
  event_storage_rep named base
    (event_mark_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros named base image row row_value group_value bit_x bit_y Hrow.
  assert (Hcomm : event_write
    (event_write image EventGrpField (Some (Z.lor group_value bit_y)))
    (event_table_field row) (Some (Z.lor row_value bit_x)) =
    event_mark_waiter image row row_value group_value bit_x bit_y).
  { apply functional_extensionality; intro f;
    unfold event_mark_waiter, event_mark_wait_row, event_write, field_update.
    destruct (EventField_eq_dec f (event_table_field row));
      destruct (EventField_eq_dec f EventGrpField); try reflexivity.
    exfalso; apply (event_table_field_not_group row); congruence. }
  rewrite <- Hcomm; unfold event_task_wait_configured_rest.
  change ((base + 10) # UChar |-> Z.lor group_value bit_y) with
    (event_cell base EventGrpField (Some (Z.lor group_value bit_y))).
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_updated_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec (event_table_field row) (event_fields named)) image
    EventGrpField (Some (Z.lor group_value bit_y)) ltac:(
      apply event_fields_remove_nodup)
    ltac:(apply in_in_remove; [intro E; apply (event_table_field_not_group row); symmetry; exact E|]
      ; destruct named; cbn [event_fields]; repeat constructor; simpl; intuition discriminate)).
  rewrite <- event_table_cell_eq by exact Hrow.
  fold (event_storage_without_field named base
    (event_write image EventGrpField (Some (Z.lor group_value bit_y)))
    (event_table_field row)).
  sep_apply_l_atomic (event_storage_merge_updated_field named base
    (event_write image EventGrpField (Some (Z.lor group_value bit_y)))
    (event_table_field row) (Some (Z.lor row_value bit_x)
    ) (event_table_field_in_fields named row)).
  entailer!.
Qed.
