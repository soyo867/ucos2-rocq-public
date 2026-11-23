Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.event
  Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.cross_module_invariants
  Ucos2Verify.lib.kernel_names Ucos2Verify.lib.task_stack Ucos2Verify.lib.event_registration.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.sem Ucos2Verify.lib.mbox Ucos2Verify.lib.queue_core.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Case-owned full-profile payload preservation. These proofs preserve the
    actual full_features profile conjunct. They neither coerce it to the
    selected profile nor establish a CPU, scheduler or interference contract. *)

Lemma event_pend_multi_event_payload_update_preserves_validity : forall sg s eid old new,
  UCOS2_full_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some old ->
  new.(eventType) = old.(eventType) -> new.(mutexFields) = old.(mutexFields) ->
  new.(waitList) = old.(waitList) -> new.(eventName) = old.(eventName) ->
  event_registered_in_range sg s.(TskState) (update_event_field_raw s.(EventState) eid new) ->
  UCOS2_full_state_inv sg (replace_EventS (update_event_field_raw s.(EventState) eid new) s).
Proof.
  intros sg s eid old new [Hprofile [Htasks [Hsched [_ [Hcross Hrest]]]]]
    Hold Htype Hmutex Hwait Hname Hevents.
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (update_event_field_raw s.(EventState) eid new) s)).
  { apply kernel_names_valid_replace_event; [tauto|].
    eapply event_update_preserves_name_references; eassumption. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (update_event_field_raw s.(EventState) eid new)).
  { eapply pending_mutex_consistency_event_fields_update with (old := old); try eassumption; tauto. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split; [exact Hevents|].
  split; [|cbn [replace_EventS]; tauto].
  eapply cross_module_registration_event_fields_update; eassumption.
Qed.

Lemma event_pend_multi_sem_count_update_preserves_validity : forall sg s eid e count,
  UCOS2_full_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_fields_consistency e.(waitList) {| semCount := count |} ->
  UCOS2_full_state_inv sg (sem_count_update_state s eid e count).
Proof.
  intros sg s eid e count Hvalid He Htype Hcount.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  eapply event_pend_multi_event_payload_update_preserves_validity; try eassumption; try reflexivity.
  pose proof Hevents as [_ [_ [_ [Hfields [_ [_ Hwait]]]]]].
  eapply event_update_preserves_in_range_with_wait; try eassumption.
  - reflexivity.
  - apply sem_set_count_preserves_fields_consistency; [exact Htype|eapply Hfields; exact He].
  - apply sem_set_count_preserves_payload_consistency; assumption.
  - unfold event_queue_id; simpl; rewrite Htype; reflexivity.
  - exact (Hwait eid e He).
Qed.

Lemma event_pend_multi_queue_update_preserves_validity : forall sg s eid node before after slots,
  UCOS2_full_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some before -> after.(qID) = before.(qID) ->
  queue_fields_consistency sg node.(waitList) after ->
  UCOS2_full_state_inv sg
    (replace_EventS (queue_update s.(EventState) eid node after slots) s).
Proof.
  intros sg s eid node before after slots
    [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]] Hnode Htype Hbefore Hsame Hqueue.
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (queue_update s.(EventState) eid node after slots) s)).
  { apply kernel_names_valid_replace_event; [tauto|].
    eapply event_update_preserves_name_references; [exact Hnode|reflexivity]. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (queue_update s.(EventState) eid node after slots)).
  { eapply pending_mutex_consistency_event_fields_update with (old := node);
      [exact Hnode|reflexivity|reflexivity|tauto]. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split.
  - pose proof Hevents as [_ [_ [_ [Hfields [_ [_ Hwait]]]]]].
    apply (event_update_preserves_in_range_with_wait sg
      (event_registered_wait_entry sg s.(TskState)) s.(EventState) eid node
      (event_set_queue_fields node after)).
    + exact Hevents.
    + exact Hnode.
    + reflexivity.
    + specialize (Hfields eid node Hnode); unfold event_fields_consistency in *;
        simpl; rewrite Htype in *; intuition discriminate.
    + unfold event_payload_consistency; simpl; rewrite Htype; exact Hqueue.
    + unfold event_queue_id; simpl; rewrite Htype, Hbefore; simpl; rewrite Hsame; reflexivity.
    + exact (Hwait eid node Hnode).
  - split; [|cbn [replace_EventS]; tauto].
    exact (cross_module_registration_event_fields_update sg s eid node
      (event_set_queue_fields node after) Hnode eq_refl eq_refl eq_refl Hcross).
Qed.

Lemma event_pend_multi_queue_dequeue_preserves_validity : forall sg s eid e q message next slots,
  UCOS2_full_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> e.(queueFields) = Some q ->
  queue_dequeue_front q = Some (message, next) ->
  UCOS2_full_state_inv sg
    (replace_EventS (queue_update s.(EventState) eid e next slots) s).
Proof.
  intros sg s eid e q message next slots Hvalid He Htype Hq Hstep.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
  rewrite Htype, Hq in Hqueue.
  pose proof (queue_dequeue_front_queue_id_eq q message next Hstep) as Hid.
  eapply event_pend_multi_queue_update_preserves_validity; try eassumption.
  eapply queue_dequeue_front_preserves_consistency_total; eauto.
Qed.
