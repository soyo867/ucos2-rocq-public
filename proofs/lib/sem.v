Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms Feq ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared count update for the existing Event-owned SemFields.  This
    neither introduces a semaphore map nor owns a resource represented by
    the count; application resource transfer needs its own protocol. *)
Definition sem_set_count (e : OSEventAbstractState) (count : Z) : OSEventAbstractState :=
  {| eventGeneration := e.(eventGeneration); eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
     eventType := e.(eventType); mutexFields := e.(mutexFields);
     semFields := Some {| semCount := count |}; mboxFields := e.(mboxFields);
     queueFields := e.(queueFields); waitList := e.(waitList) |}.

Definition sem_count_update_state (s : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) (count : Z) : UCOS2_Verify_State :=
  replace_EventS (update_event_field_raw s.(EventState) eid (sem_set_count e count)) s.

Lemma sem_set_count_same : forall e fields,
  e.(semFields) = Some fields -> sem_set_count e fields.(semCount) = e.
Proof.
  intros e [count] H; destruct e; simpl in H; subst; reflexivity.
Qed.

Lemma sem_set_count_last_write : forall e first last,
  sem_set_count (sem_set_count e first) last = sem_set_count e last.
Proof. reflexivity. Qed.

Lemma sem_set_count_preserves_fields_consistency : forall e count,
  e.(eventType) = OS_EVENT_TYPE_SEM -> event_fields_consistency e ->
  event_fields_consistency (sem_set_count e count).
Proof.
  intros e count Htype Hfields; unfold event_fields_consistency in *;
    simpl; rewrite Htype in *; intuition discriminate.
Qed.

Lemma sem_set_count_preserves_payload_consistency : forall sg e count,
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_fields_consistency e.(waitList) {| semCount := count |} ->
  event_payload_consistency sg (sem_set_count e count).
Proof.
  intros sg e count Htype Hcount; unfold event_payload_consistency; simpl;
    rewrite Htype; exact Hcount.
Qed.

Lemma sem_positive_count_no_waiters : forall waiters fields,
  sem_fields_consistency waiters fields -> 0 < fields.(semCount) -> waiters = [].
Proof.
  intros waiters fields [Hrange Hempty] Hpositive.
  destruct waiters as [|head tail]; [reflexivity|].
  specialize (Hempty ltac:(discriminate)); lia.
Qed.

Lemma sem_decrement_preserves_consistency : forall waiters fields,
  sem_fields_consistency waiters fields -> 0 < fields.(semCount) ->
  sem_fields_consistency waiters {| semCount := fields.(semCount) - 1 |}.
Proof.
  intros waiters fields Hvalid Hpositive.
  pose proof (sem_positive_count_no_waiters waiters fields Hvalid Hpositive) as ->.
  destruct Hvalid as [Hrange _]; split; [simpl; lia|intros H; contradiction].
Qed.

Lemma sem_increment_preserves_consistency : forall fields,
  sem_fields_consistency [] fields -> fields.(semCount) < 65535 ->
  sem_fields_consistency [] {| semCount := fields.(semCount) + 1 |}.
Proof.
  intros fields [Hrange _] Hroom; split; [simpl; lia|intros H; contradiction].
Qed.

Lemma sem_set_count_preserves_event_in_range : forall sg tasks events eid e count,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_fields_consistency e.(waitList) {| semCount := count |} ->
  event_in_range sg tasks (update_event_field_raw events eid (sem_set_count e count)).
Proof.
  intros sg tasks events eid e count Hvalid He Htype Hcount.
  pose proof Hvalid as [_ [_ [_ [Hfields [_ [_ Hwait]]]]]].
  eapply event_update_preserves_in_range; try eassumption.
  - reflexivity.
  - apply sem_set_count_preserves_fields_consistency; [exact Htype|eapply Hfields; exact He].
  - apply sem_set_count_preserves_payload_consistency; assumption.
  - unfold event_queue_id; simpl; rewrite Htype; reflexivity.
  - exact (Hwait eid e He).
Qed.

Definition sem_rep_no_count (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks e) EventCntField.

Lemma sem_rep_split_count : forall sg tasks eid e fields,
  e.(eventType) = OS_EVENT_TYPE_SEM -> e.(semFields) = Some fields ->
  used_event_rep sg tasks eid e |--
  (event_addr sg eid + OSEventCnt_off) # UShort |-> fields.(semCount) **
  sem_rep_no_count sg tasks eid e.
Proof.
  intros sg tasks eid e fields Htype Hfields.
  unfold used_event_rep, sem_rep_no_count.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks e) EventCntField ltac:(simpl; tauto)).
  cbn [event_image event_cell event_field_offset].
  unfold encode_event_cnt_value; rewrite Htype, Hfields.
  unfold OSEventCnt_off; simpl; entailer!.
Qed.

Lemma sem_set_count_image_eq : forall sg tasks e count,
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  event_image sg tasks (sem_set_count e count) =
  event_write (event_image sg tasks e) EventCntField (Some count).
Proof.
  intros sg tasks e count Htype; apply functional_extensionality; intros [].
  all: cbn [event_image event_write field_update sem_set_count]; try reflexivity.
  all: unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value, encode_event_cnt_value;
    simpl; rewrite Htype; reflexivity.
Qed.

Lemma sem_rep_merge_updated_count : forall sg tasks eid e count,
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
  sem_rep_no_count sg tasks eid e |-- used_event_rep sg tasks eid (sem_set_count e count).
Proof.
  intros sg tasks eid e count Htype; unfold used_event_rep, sem_rep_no_count.
  rewrite (sem_set_count_image_eq sg tasks e count Htype).
  apply (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks e) EventCntField (Some count) ltac:(simpl; tauto)).
Qed.

Lemma sem_rep_merge_count : forall sg tasks eid e fields,
  e.(eventType) = OS_EVENT_TYPE_SEM -> e.(semFields) = Some fields ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> fields.(semCount) **
  sem_rep_no_count sg tasks eid e |-- used_event_rep sg tasks eid e.
Proof.
  intros sg tasks eid e fields Htype Hfields.
  pose proof (sem_rep_merge_updated_count sg tasks eid e fields.(semCount) Htype) as Hmerge.
  rewrite (sem_set_count_same e fields Hfields) in Hmerge; exact Hmerge.
Qed.
