Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.sem.

Import ListNotations EventStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A function-local view of the existing full ECB inventory. No cells are
    discarded: padding, group/table bytes and the optional name remain owned. *)
Definition sem_accept_event_rest_fields (named : bool) : list EventField :=
  remove EventField_eq_dec EventCntField
    (remove EventField_eq_dec EventPtrField
      (remove EventField_eq_dec EventTypeField (event_fields named))).

Definition sem_accept_event_rest_storage (named : bool) (base : addr)
  (image : EventStorage) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (sem_accept_event_rest_fields named) image.

Lemma sem_accept_event_fields_reorder : forall named base image,
  event_storage_rep named base image =
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (EventTypeField :: EventPtrField :: EventCntField ::
      sem_accept_event_rest_fields named) image.
Proof.
  intros named base image; unfold event_storage_rep,
    EventFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intro field.
  destruct named, field; reflexivity.
Qed.

Lemma sem_accept_event_fields_nodup : forall named,
  NoDup (EventTypeField :: EventPtrField :: EventCntField ::
    sem_accept_event_rest_fields named).
Proof.
  intros []; unfold sem_accept_event_rest_fields, event_fields; simpl.
  all: repeat (apply NoDup_cons; [simpl; intuition discriminate|]).
  all: apply NoDup_nil.
Qed.

Lemma sem_accept_event_storage_core_fields : forall named base image,
  event_storage_rep named base image --||--
  event_cell base EventTypeField (image EventTypeField) **
  event_cell base EventPtrField (image EventPtrField) **
  event_cell base EventCntField (image EventCntField) **
  sem_accept_event_rest_storage named base image.
Proof.
  intros named base image.
  rewrite sem_accept_event_fields_reorder.
  pose proof (sem_accept_event_fields_nodup named) as Htype.
  pose proof Htype as Hptr; apply NoDup_cons_iff in Hptr; destruct Hptr as [_ Hptr].
  pose proof Hptr as Hcnt; apply NoDup_cons_iff in Hcnt; destruct Hcnt as [_ Hcnt].
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ image EventTypeField Htype).
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ image EventPtrField Hptr).
  rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec
    (event_cell base) _ image EventCntField Hcnt).
  unfold sem_accept_event_rest_storage; split; entailer!.
Qed.

Lemma sem_accept_event_rest_storage_count_update : forall named base image count,
  sem_accept_event_rest_storage named base
    (event_write image EventCntField (Some count)) =
  sem_accept_event_rest_storage named base image.
Proof.
  intros; unfold sem_accept_event_rest_storage, event_write.
  apply EventFieldStorage.store_fields_update_unlisted.
  unfold sem_accept_event_rest_fields; apply remove_In.
Qed.

Lemma sem_accept_event_storage_merge_updated_count : forall named base image count,
  event_cell base EventTypeField (image EventTypeField) **
  event_cell base EventPtrField (image EventPtrField) **
  event_cell base EventCntField (Some count) **
  sem_accept_event_rest_storage named base image |--
  event_storage_rep named base (event_write image EventCntField (Some count)).
Proof.
  intros named base image count.
  rewrite sem_accept_event_storage_core_fields.
  rewrite sem_accept_event_rest_storage_count_update.
  cbn [event_write field_update EventField_eq_dec].
  apply derivable1_refl.
Qed.

Definition sem_accept_event_rest_full (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : EventID) (e : OSEventAbstractState)
  : Assertion :=
  sem_accept_event_rest_storage sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg tasks e).

Lemma sem_accept_event_rep_core_fields : forall sg tasks eid e,
  used_event_rep sg tasks eid e --||--
  (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg e **
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
  sem_accept_event_rest_full sg tasks eid e.
Proof.
  intros; unfold used_event_rep, sem_accept_event_rest_full.
  rewrite sem_accept_event_storage_core_fields.
  cbn [event_image event_cell event_field_offset].
  reflexivity.
Qed.

Lemma sem_accept_event_rep_merge_updated_count : forall sg tasks eid e count,
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg e **
  (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
  sem_accept_event_rest_full sg tasks eid e |--
  used_event_rep sg tasks eid (sem_set_count e count).
Proof.
  intros sg tasks eid e count Hsem.
  unfold used_event_rep, sem_accept_event_rest_full.
  rewrite sem_set_count_image_eq by exact Hsem.
  change
    (event_cell (event_addr sg eid) EventTypeField
       ((event_image sg tasks e) EventTypeField) **
     event_cell (event_addr sg eid) EventPtrField
       ((event_image sg tasks e) EventPtrField) **
     event_cell (event_addr sg eid) EventCntField (Some count) **
     sem_accept_event_rest_storage
       (cfgEventNames (osKernelConfig sg)) (event_addr sg eid)
       (event_image sg tasks e) |--
     event_storage_rep (cfgEventNames (osKernelConfig sg))
       (event_addr sg eid)
       (event_write (event_image sg tasks e) EventCntField (Some count))).
  apply sem_accept_event_storage_merge_updated_count.
Qed.
