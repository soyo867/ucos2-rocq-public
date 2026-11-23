Require Export Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Export Ucos2Verify.VC.code.tick.spec.time_tick_sched_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.ucos2_verify_inv.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSSemPost at its actual nested ISR call.  The opened critical owner is
    borrowed across token-only Save/Restore, and across the no-switch
    Scheduler call.  The state relation records the actual wake request. *)
Definition time_tick_sem_result sg pointer before error after : Prop :=
  exists result, encode_os_err_code (fst result) = error /\
    time_tick_post_call sg pointer before result after.

Definition time_tick_sem_type (node : OSEventAbstractState) : Z :=
  encode_event_type node.(eventType).

Definition time_tick_internal_addresses sg interrupt_address priority_address
  unmap_address group_address rows_address : Prop :=
  sg.(g_OSIntNesting) = interrupt_address /\
  sg.(g_OSTCBPrioTbl) = priority_address /\
  sg.(g_OSUnMapTbl) = unmap_address /\
  sg.(g_OSRdyGrp) = group_address /\ sg.(g_OSRdyTbl) = rows_address.

Definition time_tick_sem_ready_group (state : UCOS2_Verify_State) : Z :=
  encode_ready_grp state.(SchedState).(readyList) state.(TskState).

Definition time_tick_sem_ready_rows (state : UCOS2_Verify_State) : list Z :=
  sched_row_values state.(TskState) state.(SchedState).(readyList).

Lemma time_tick_sem_null_result : forall sg before,
  sem_post_profile sg -> time_tick_sem_result sg 0 before 4 before.
Proof.
  intros sg before Hprofile; exists (OS_ERR_PEVENT_NULL, false).
  split; [reflexivity|apply time_tick_post_argument_error].
  unfold sem_post_argument_error, sem_post_profile in *.
  rewrite Hprofile, Z.eqb_refl; reflexivity.
Qed.

Lemma time_tick_sem_nonnull_argument : forall sg pointer,
  pointer <> 0 -> sem_post_argument_error sg pointer = None.
Proof.
  intros sg pointer Hpointer; unfold sem_post_argument_error.
  rewrite (proj2 (Z.eqb_neq pointer 0) Hpointer), Bool.andb_false_r; reflexivity.
Qed.

Lemma time_tick_sem_readable_nonnull : forall sg before pointer,
  UCOS2_state_inv sg before -> time_tick_post_readable sg before pointer ->
  pointer <> 0 -> exists eid node,
    pointer = event_addr sg eid /\ valid_event_id sg eid /\
    sem_post_lookup before eid node.
Proof.
  intros sg before pointer Hvalid Hread Hnonnull.
  destruct Hread as [[error Herror]|[eid [node [Hpointer Hnode]]]].
  - rewrite (time_tick_sem_nonnull_argument sg pointer Hnonnull) in Herror;
      discriminate.
  - pose proof Hvalid as [_ [_ [_ [[Hpartition _] _]]]].
    pose proof (proj1 (event_pool_used_not_free sg before.(EventState) eid node
      Hpartition Hnode)) as Hrange.
    exists eid, node; split; [exact Hpointer|split; assumption].
Qed.

Lemma time_tick_sem_type_split : forall sg before eid node,
  sem_post_lookup before eid node ->
  UCOS2_inv sg before |-- coq_prop (UCOS2_state_inv sg before) &&
    ((event_addr sg eid + OSEventType_off) # UChar |-> time_tick_sem_type node **
      sem_post_type_frame sg before eid node).
Proof.
  intros sg before eid node Hnode.
  exact (sem_post_field_split_full sg before eid node EventTypeField
    Hnode ltac:(simpl; tauto)).
Qed.

Lemma time_tick_sem_type_merge : forall sg before eid node,
  UCOS2_state_inv sg before -> sem_post_lookup before eid node ->
  (event_addr sg eid + OSEventType_off) # UChar |-> time_tick_sem_type node **
    sem_post_type_frame sg before eid node |-- UCOS2_inv sg before.
Proof.
  intros sg before eid node Hvalid Hnode.
  exact (sem_post_field_merge_full sg before eid node EventTypeField
    Hvalid Hnode ltac:(simpl; tauto)).
Qed.

Lemma time_tick_sem_type_range : forall node,
  0 <= time_tick_sem_type node <= 255.
Proof. intros; unfold time_tick_sem_type; destruct node.(eventType); simpl; lia. Qed.

Lemma time_tick_sem_type_is_sem : forall node,
  time_tick_sem_type node = 3 -> node.(eventType) = OS_EVENT_TYPE_SEM.
Proof.
  intros node Htype; unfold time_tick_sem_type in Htype.
  destruct node.(eventType); simpl in Htype; try discriminate; reflexivity.
Qed.

Lemma time_tick_sem_type_error_result : forall sg pointer before eid node,
  pointer <> 0 -> pointer = event_addr sg eid ->
  sem_post_lookup before eid node -> time_tick_sem_type node <> 3 ->
  time_tick_sem_result sg pointer before 1 before.
Proof.
  intros sg pointer before eid node Hnonnull Hpointer Hnode Htype.
  exists (OS_ERR_EVENT_TYPE, false); split; [reflexivity|].
  eapply time_tick_post_type_error with (eid := eid) (e := node).
  - apply time_tick_sem_nonnull_argument; exact Hnonnull.
  - exact Hpointer.
  - exact Hnode.
  - assert (Hnot : Z.eqb (encode_event_type node.(eventType))
        (encode_event_type OS_EVENT_TYPE_SEM) = false).
    { apply Z.eqb_neq; exact Htype. }
    unfold sem_post_type_error; rewrite Hnot; reflexivity.
Qed.

Lemma time_tick_sem_group_split : forall sg before eid node,
  sem_post_lookup before eid node ->
  UCOS2_inv sg before |-- coq_prop (UCOS2_state_inv sg before) &&
    ((event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group before node **
      sem_post_group_frame sg before eid node).
Proof.
  intros sg before eid node Hnode.
  exact (sem_post_field_split_full sg before eid node EventGrpField
    Hnode ltac:(simpl; tauto)).
Qed.

Lemma time_tick_sem_group_merge : forall sg before eid node,
  UCOS2_state_inv sg before -> sem_post_lookup before eid node ->
  (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group before node **
    sem_post_group_frame sg before eid node |-- UCOS2_inv sg before.
Proof.
  intros sg before eid node Hvalid Hnode.
  exact (sem_post_field_merge_full sg before eid node EventGrpField
    Hvalid Hnode ltac:(simpl; tauto)).
Qed.

Lemma time_tick_sem_critical_result : forall sg pointer before eid node result after,
  pointer <> 0 -> pointer = event_addr sg eid ->
  sem_post_lookup before eid node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_critical sg eid before result after ->
  time_tick_sem_result sg pointer before (encode_os_err_code (fst result)) after.
Proof.
  intros sg pointer before eid node result after Hnonnull Hpointer Hnode Htype Hstep.
  exists result; split; [reflexivity|].
  eapply time_tick_post_critical with (eid := eid) (e := node).
  - apply time_tick_sem_nonnull_argument; exact Hnonnull.
  - exact Hpointer.
  - exact Hnode.
  - unfold sem_post_type_error; rewrite Htype; reflexivity.
  - exact Hstep.
Qed.

Lemma time_tick_sem_result_interrupts : forall sg pointer before error after,
  UCOS2_state_inv sg before -> time_tick_sem_result sg pointer before error after ->
  os_sched_ints after = os_sched_ints before.
Proof.
  intros sg pointer before error after Hvalid [result [Herror Hcall]].
  pose proof (proj1 (time_tick_post_call_intr_timer_eq sg pointer before result after
    Hcall Hvalid)) as Hframe.
  unfold os_sched_ints; rewrite Hframe; reflexivity.
Qed.
