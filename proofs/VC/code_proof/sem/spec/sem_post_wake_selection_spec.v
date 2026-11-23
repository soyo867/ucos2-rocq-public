Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.

(** A present-state selection fact for the actual SemPost wake branch.
    The suspension test and priorities are those read by EventTaskRdy and
    OS_SchedNew. No assumption says that a saved invocation will eventually
    execute, or that an arbitrary awakened task immediately preempts.
    Other ready orders keep their ordinary selector behavior. *)
Lemma sem_post_wake_selects_highest_waiter :
  forall sg entry eid event tid old current_slot current,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_status_is_suspended
    (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)) = false ->
  (forall slot node, In slot entry.(SchedState).(readyList) ->
    entry.(TskState).(inUsedTaskStates) slot = Some node -> old.(curPrio) < node.(curPrio)) ->
  sched_current_ready_at entry.(TskState) entry.(SchedState) current_slot current ->
  entry.(IntrState).(intNesting) = 0 -> entry.(IntrState).(lockNesting) = 0 ->
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  checkpoint.(SchedState).(readyList) = tid :: remove_Z_eqb tid entry.(SchedState).(readyList) /\
  checkpoint.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old PendSem 0 PendOK) /\
  os_sched_requests_switch checkpoint = true /\
  selected.(SchedState).(highRdyTid) = Some tid /\
  selected.(SchedState).(highRdyPrio) = Some old.(curPrio).
Proof.
  intros sg entry eid event tid old current_slot current Hvalid Hlookup Htype Hentry
    Hunsuspended Hhighest Hcurrent Hnest Hlock checkpoint selected.
  pose proof Hentry as [Hsg [_ [_ [_ [_ [Hwait_head Hold]]]]]].
  pose proof Hvalid as [_ [_ [[Hready _] _]]].
  pose proof Hready as [Hmembers _].
  assert (Hhead : checkpoint.(SchedState).(readyList) =
    tid :: remove_Z_eqb tid entry.(SchedState).(readyList)).
  { change ((sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
      (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).(readyList) =
      tid :: remove_Z_eqb tid entry.(SchedState).(readyList)).
    unfold sched_wake_by_status; rewrite Hunsuspended; cbn [sched_set_ready readyList].
    destruct (remove_Z_eqb tid entry.(SchedState).(readyList)) as [|head tail] eqn:Hremoved;
      [reflexivity|].
    cbn [insert_sorted_by].
    assert (Hin : In head entry.(SchedState).(readyList)).
    { apply (remove_Z_eqb_in tid head entry.(SchedState).(readyList)).
      rewrite Hremoved; left; reflexivity. }
    destruct (Hmembers head Hin) as [node [Hnode Hnode_rest]].
    assert (Hlt : old.(curPrio) <? node.(curPrio) = true)
      by (apply Z.ltb_lt; eapply Hhighest; eassumption).
    unfold sched_task_key; rewrite Hold, Hnode, Hlt; reflexivity. }
  assert (Hnode : checkpoint.(TskState).(inUsedTaskStates) tid =
    Some (task_event_wake_single old PendSem 0 PendOK)).
  { change ((if Z.eqb tid tid then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) tid) = Some (task_event_wake_single old PendSem 0 PendOK)).
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hin_wait : In tid event.(waitList)).
  { destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
    inversion Hwait_head; subst head; left; reflexivity. }
  assert (Hvalid_after : UCOS2_state_inv sg checkpoint).
  { apply UCOS2_event_wake_preserves_validity; [exact Hvalid|exact Hlookup|
      exact Hin_wait|exact Hold|rewrite Htype; reflexivity]. }
  pose proof Hvalid_after as [_ [_ [[Hready_after _] _]]].
  assert (Hpriority : sched_selected_priority checkpoint.(TskState) checkpoint.(SchedState) = old.(curPrio)).
  { change (sched_selected_priority checkpoint.(TskState) checkpoint.(SchedState) =
      (task_event_wake_single old PendSem 0 PendOK).(curPrio)).
    eapply sched_selected_priority_eq_head; eassumption. }
  assert (Henabled : os_sched_selection_enabled checkpoint = true).
  { apply os_sched_selection_enabled_iff; split; assumption. }
  destruct Hcurrent as [Hcurrent_node [_ [Hcurrent_priority [Hcurrent_ready _]]]].
  assert (Hcurrent_after : checkpoint.(SchedState).(curSchedPrio) = Some current.(curPrio)).
  { change ((sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
      (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).(curSchedPrio) =
      Some current.(curPrio)).
    unfold sched_wake_by_status; rewrite Hunsuspended; exact Hcurrent_priority. }
  assert (Hswitch : os_sched_requests_switch checkpoint = true).
  { apply os_sched_requests_switch_iff; split; [exact Henabled|].
    rewrite Hpriority, Hcurrent_after; cbn [sched_priority_byte].
    pose proof (Hhighest current_slot current Hcurrent_ready Hcurrent_node); lia. }
  split; [exact Hhead|]. split; [exact Hnode|]. split; [exact Hswitch|].
  unfold selected, os_sched_prefix_state; cbn [replace_SchedS SchedState].
  unfold os_sched_ready_checkpoint; rewrite Henabled, Hswitch.
  cbn [sched_increment_switch_counter highRdyTid highRdyPrio].
  unfold sched_refresh_high; cbn [highRdyTid highRdyPrio]; rewrite Hhead, Hnode.
  split; reflexivity.
Qed.
