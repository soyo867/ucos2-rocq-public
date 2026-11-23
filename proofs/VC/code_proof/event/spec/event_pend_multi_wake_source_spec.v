Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_source_transport_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_full_spec.
Import ListNotations TaskStateDef EventStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The typed wake transformer is related to the actual full-layout
    EventTaskRdy image, including EventPtr's preceding single removal.
    Only the MultiPtr-non-NULL branch has this endpoint. *)
Lemma event_pend_multi_wake_source_task_image_eq :
  forall sg task selected kind message result,
  task.(tcbEventMultiPtr) <> 0 ->
  event_task_rdy_full_task_image sg task selected message (task_pend_mask kind)
    (encode_pend_status result) =
  task_layout_image sg (task_multi_wake task kind message result selected).
Proof.
  intros sg task selected kind message result Hlinked.
  rewrite task_multi_wake_layout_image_eq.
  unfold event_task_rdy_full_task_image.
  destruct (Z.eq_dec task.(tcbEventMultiPtr) 0); [contradiction|].
  apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; reflexivity.
Qed.

Lemma event_pend_multi_wake_source_events_eq :
  forall events selected node tid task instances,
  events.(inUsedEventStates) selected = Some node -> task.(tcbEventMultiPtr) <> 0 ->
  task.(eventMultiWaitEvents) = map fst instances ->
  event_task_rdy_full_events events selected node tid task instances =
  event_multi_remove_waiters events tid (selected :: task.(eventMultiWaitEvents)).
Proof.
  intros events selected node tid task instances Hnode Hlinked Hids.
  unfold event_task_rdy_full_events.
  destruct (Z.eq_dec task.(tcbEventMultiPtr) 0); [contradiction|].
  unfold event_task_remove_multi_events, event_task_rdy_full_after_remove.
  rewrite Hids, (event_multi_remove_waiters_source_order events tid selected
    (map fst instances) node Hnode); reflexivity.
Qed.

(** The full callee's checked array binding justifies every actual loop
    dereference. The original sequence equality is a caller-side array
    interpretation, not a requirement that historical wake ids stay live. *)
Lemma event_pend_multi_wake_source_atomic_step :
  forall sg state selected node tid task pointers instances kind message result,
  event_task_rdy_full_entry sg state.(TskState) state.(EventState)
    selected node tid task pointers instances ->
  task.(tcbEventMultiPtr) <> 0 -> task.(eventMultiWaitEvents) = map fst instances ->
  atomic_event_task_wake_multi sg tid selected kind message result state tt
    (event_multi_wake_state sg state tid task selected kind message result
      (event_task_rdy_full_events state.(EventState) selected node tid task instances)).
Proof.
  intros sg state selected node tid task pointers instances kind message result
    [_ [_ [Hnode [_ [_ [_ [Htask Hinput]]]]]]] Hlinked Hids.
  rewrite (event_pend_multi_wake_source_events_eq _ _ _ _ _ _ Hnode Hlinked Hids).
  destruct (Hinput Hlinked) as [_ [_ [_ [_ [_ [Hbinding _]]]]]].
  eapply atomic_event_task_wake_multi_from_binding; eassumption.
Qed.

Lemma event_pend_multi_wake_source_post_image :
  forall sg tasks events selected node tid task pointers instances kind message result group rows returned,
  events.(inUsedEventStates) selected = Some node -> task.(tcbEventMultiPtr) <> 0 ->
  task.(eventMultiWaitEvents) = map fst instances ->
  event_task_rdy_full_post sg tasks events selected node tid task pointers instances
    message (task_pend_mask kind) (encode_pend_status result) group rows returned |--
  coq_prop (returned = event_wait_priority tasks node /\ returned = task.(curPrio)) &&
  (tcb_configured_storage_rep true true (task_slot_addr sg tid)
     (task_layout_image sg (task_multi_wake task kind message result selected)) **
   event_raw_rep sg tasks
     (event_multi_remove_waiters events tid (selected :: task.(eventMultiWaitEvents))) **
   event_multi_array_rep task.(tcbEventMultiPtr) pointers **
   unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
   event_task_rdy_full_ready sg task (task_pend_mask kind) group rows).
Proof.
  intros sg tasks events selected node tid task pointers instances kind message result
    group rows returned Hnode Hlinked Hids.
  unfold event_task_rdy_full_post.
  rewrite (event_pend_multi_wake_source_task_image_eq _ _ _ _ _ _ Hlinked),
    (event_pend_multi_wake_source_events_eq _ _ _ _ _ _ Hnode Hlinked Hids).
  unfold event_task_rdy_full_array; destruct (Z.eq_dec task.(tcbEventMultiPtr) 0);
    [contradiction|reflexivity].
Qed.
