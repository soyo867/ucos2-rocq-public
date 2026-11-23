Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.error_codes.

Import ListNotations.
Import EventStateDef.
Local Open Scope Z_scope.

(** OSSemSet updates the canonical semaphore payload of one live OS_EVENT;
    it does not introduce a parallel semaphore state. *)
Definition sem_set_updated_event
  (e : OSEventAbstractState) (cnt : Z) : OSEventAbstractState :=
  {| eventGeneration := e.(eventGeneration);
     eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
     eventType   := e.(eventType);
     mutexFields := e.(mutexFields);
     semFields   := Some {| semCount := cnt |};
     mboxFields  := e.(mboxFields);
     queueFields := e.(queueFields);
     waitList    := e.(waitList) |}.

Definition sem_set_updated_event_state
  (evs : Glob_EventAbstractState) (eid : EventID)
  (e : OSEventAbstractState) (cnt : Z) : Glob_EventAbstractState :=
  update_event_field_raw evs eid (sem_set_updated_event e cnt).

Definition sem_set_post_state
  (ls : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) (cnt : Z) : UCOS2_Verify_State :=
  replace_EventS
    (sem_set_updated_event_state ls.(EventState) eid e cnt) ls.

(** Ordered public semantics for the selected non-safety-critical profile:
    null, wrong type, successful count write, then waiting-task rejection. *)
Definition OSSemSet_sem
  (sg : StableGlobVars) (pevent : addr) (cnt : Z)
  : program UCOS2_Verify_State OSErrCode :=
  fun ls0 err ls1 =>
    (pevent = 0 /\
     err = OS_ERR_PEVENT_NULL /\
     ls1 = ls0) \/
    (pevent <> 0 /\
     exists eid e,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) <> OS_EVENT_TYPE_SEM /\
       err = OS_ERR_EVENT_TYPE /\
       ls1 = ls0) \/
    (pevent <> 0 /\
     exists eid e sf,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       (sf.(semCount) > 0 \/
        encode_event_wait_grp e.(waitList) ls0.(TskState) = 0) /\
       err = OS_ERR_NONE /\
       ls1 = sem_set_post_state ls0 eid e cnt) \/
    (pevent <> 0 /\
     exists eid e sf,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       sf.(semCount) = 0 /\
       encode_event_wait_grp e.(waitList) ls0.(TskState) <> 0 /\
       err = OS_ERR_TASK_WAITING /\
       ls1 = ls0).

Definition sem_set_observe_err (err : OSErrCode)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X0 n X1 => n = encode_os_err_code err /\ X1 = X0.

Definition sem_set_result_prop
  (pevent etype old_cnt event_grp err : Z) : Prop :=
  (pevent = 0 /\ err = encode_os_err_code OS_ERR_PEVENT_NULL) \/
  (pevent <> 0 /\ etype <> encode_event_type OS_EVENT_TYPE_SEM /\
   err = encode_os_err_code OS_ERR_EVENT_TYPE) \/
  (pevent <> 0 /\ etype = encode_event_type OS_EVENT_TYPE_SEM /\
   (old_cnt > 0 \/ event_grp = 0) /\
   err = encode_os_err_code OS_ERR_NONE) \/
  (pevent <> 0 /\ etype = encode_event_type OS_EVENT_TYPE_SEM /\
   old_cnt = 0 /\ event_grp <> 0 /\
   err = encode_os_err_code OS_ERR_TASK_WAITING).

(** The registered interrupt abstraction models Save/Restore as preserving
    the OS state.  It deliberately does not claim hardware-token pairing. *)
Definition sem_set_enter_transition_prop
  (entry inside : UCOS2_Verify_State) : Prop :=
  crit_rel_no_os_state_change entry inside.

Definition sem_set_restore_transition_prop
  (entry inside restored : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (cnt : Z)
  (old_cnt event_grp : Z) : Prop :=
  sem_set_enter_transition_prop entry inside /\
  (((old_cnt > 0 \/ event_grp = 0) /\
    restored = sem_set_post_state entry eid e cnt) \/
   (old_cnt <= 0 /\ event_grp <> 0 /\ restored = entry)) /\
  crit_rel_event_only entry restored.

Lemma sem_set_restore_transition_total :
  forall entry inside eid e cnt old_cnt event_grp,
    sem_set_enter_transition_prop entry inside ->
    exists restored,
      sem_set_restore_transition_prop
        entry inside restored eid e cnt old_cnt event_grp.
Proof.
  intros entry inside eid e cnt old_cnt event_grp Henter.
  destruct (Z_gt_dec old_cnt 0) as [Hpos | Hnpos].
  - exists (sem_set_post_state entry eid e cnt).
    unfold sem_set_restore_transition_prop.
    split; [exact Henter |].
    split.
    + left. split; [left; exact Hpos | reflexivity].
    + unfold crit_rel_event_only, sem_set_post_state.
      destruct entry; reflexivity.
  - destruct (Z.eq_dec event_grp 0) as [Hzero | Hnonzero].
    + exists (sem_set_post_state entry eid e cnt).
      unfold sem_set_restore_transition_prop.
      split; [exact Henter |].
      split.
      * left. split; [right; exact Hzero | reflexivity].
      * unfold crit_rel_event_only, sem_set_post_state.
        destruct entry; reflexivity.
    + exists entry.
      unfold sem_set_restore_transition_prop.
      split; [exact Henter |].
      split.
      * right. split; [lia |]. split; [exact Hnonzero | reflexivity].
      * unfold crit_rel_event_only. destruct entry; reflexivity.
Qed.

Lemma sem_set_updated_event_type :
  forall e cnt,
    (sem_set_updated_event e cnt).(eventType) = e.(eventType).
Proof. reflexivity. Qed.

Lemma sem_set_updated_event_waitList :
  forall e cnt,
    (sem_set_updated_event e cnt).(waitList) = e.(waitList).
Proof. reflexivity. Qed.

Lemma sem_set_updated_event_count_encoding :
  forall e cnt,
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    encode_event_cnt_value (sem_set_updated_event e cnt) = cnt.
Proof.
  intros e cnt Htype.
  unfold encode_event_cnt_value, sem_set_updated_event; simpl.
  rewrite Htype. reflexivity.
Qed.

Lemma sem_set_updated_event_state_lookup_eq :
  forall evs eid e cnt,
    (sem_set_updated_event_state evs eid e cnt).(inUsedEventStates) eid =
      Some (sem_set_updated_event e cnt).
Proof.
  intros. unfold sem_set_updated_event_state, update_event_field_raw.
  simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma sem_set_updated_event_state_lookup_neq :
  forall evs eid e cnt eid',
    eid' <> eid ->
    (sem_set_updated_event_state evs eid e cnt).(inUsedEventStates) eid' =
      evs.(inUsedEventStates) eid'.
Proof.
  intros evs eid e cnt eid' Hneq.
  unfold sem_set_updated_event_state, update_event_field_raw.
  simpl. destruct (Z.eqb eid' eid) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma sem_set_payload_consistency_preserved :
  forall sg e sf cnt,
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    e.(semFields) = Some sf ->
    event_payload_consistency sg e ->
    0 <= cnt <= 65535 ->
    (sf.(semCount) > 0 \/ e.(waitList) = []) ->
    event_payload_consistency sg (sem_set_updated_event e cnt).
Proof.
  intros sg e sf cnt Htype Hsf Hpayload Hcnt Hwrite.
  unfold event_payload_consistency in *.
  rewrite Htype, Hsf in Hpayload. simpl in Hpayload.
  unfold sem_set_updated_event. simpl. rewrite Htype. simpl.
  split; [exact Hcnt |].
  intros Hwait.
  destruct Hwrite as [Hpositive | Hempty].
  - destruct Hpayload as [_ Hold_wait].
    specialize (Hold_wait Hwait). lia.
  - contradiction.
Qed.

Lemma sem_set_wait_grp_zero_implies_empty :
  forall sg tskSt wl,
    event_waitList_canonical sg tskSt wl ->
    encode_event_wait_grp wl tskSt = 0 ->
    wl = [].
Proof.
  intros sg tskSt wl Hcanonical Hgrp.
  destruct wl as [|tid rest]; [reflexivity |].
  destruct Hcanonical as [_ [_ Hrange]].
  destruct (Hrange tid ltac:(left; reflexivity))
    as [t [Hget Hprio]].
  cbn in Hgrp. rewrite Hget in Hgrp.
  apply Z.lor_eq_0_iff in Hgrp.
  destruct Hgrp as [Hbit _].
  rewrite Z.shiftl_1_l in Hbit.
  unfold valid_task_prio in Hprio.
  assert (Hdiv_nonneg : 0 <= t.(curPrio) / 8).
  { apply Z_div_nonneg_nonneg; lia. }
  pose proof
    (Z.pow_pos_nonneg 2 (t.(curPrio) / 8) ltac:(lia) Hdiv_nonneg).
  lia.
Qed.

Lemma sem_set_payload_consistency_preserved_encoded :
  forall sg tskSt e sf cnt,
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    e.(semFields) = Some sf ->
    event_payload_consistency sg e ->
    event_waitList_canonical sg tskSt e.(waitList) ->
    0 <= cnt <= 65535 ->
    (sf.(semCount) > 0 \/
     encode_event_wait_grp e.(waitList) tskSt = 0) ->
    event_payload_consistency sg (sem_set_updated_event e cnt).
Proof.
  intros sg tskSt e sf cnt Htype Hsf Hpayload Hcanonical Hcnt Hwrite.
  eapply sem_set_payload_consistency_preserved; eauto.
  destruct Hwrite as [Hpositive | Hgrp].
  - left; exact Hpositive.
  - right. eapply sem_set_wait_grp_zero_implies_empty; eauto.
Qed.

Lemma sem_set_wait_entry_consistency_preserved :
  forall sg tskSt eid e cnt,
    verification_slice_event_wait_entry_consistency sg tskSt eid e ->
    verification_slice_event_wait_entry_consistency
      sg tskSt eid (sem_set_updated_event e cnt).
Proof.
  intros sg tskSt eid e cnt Hcons.
  unfold verification_slice_event_wait_entry_consistency in *.
  unfold sem_set_updated_event; simpl.
  exact Hcons.
Qed.

Lemma sem_set_preserves_event_wait_object_consistency__sem_set_all :
  forall sg ls eid e cnt,
    ls.(EventState).(inUsedEventStates) eid = Some e ->
    verification_slice_event_wait_object_consistency sg ls ->
    verification_slice_event_wait_object_consistency sg (sem_set_post_state ls eid e cnt).
Proof.
  intros sg ls eid e cnt Hget [Hentry [Hback Hclosed]].
  split; [| split].
  - intros i v Hi.
    change (inUsedEventStates
      (sem_set_updated_event_state (EventState ls) eid e cnt) i = Some v) in Hi.
    destruct (Z.eq_dec i eid) as [Heq | Hneq].
    + subst i. rewrite sem_set_updated_event_state_lookup_eq in Hi.
      injection Hi as Hv. subst v.
      apply sem_set_wait_entry_consistency_preserved. apply Hentry. exact Hget.
    + rewrite sem_set_updated_event_state_lookup_neq in Hi by exact Hneq.
      exact (Hentry i v Hi).
  - intros tid t i v Ht Hi Href.
    change (inUsedEventStates
      (sem_set_updated_event_state (EventState ls) eid e cnt) i = Some v) in Hi.
    destruct (Z.eq_dec i eid) as [Heq | Hneq].
    + subst i. rewrite sem_set_updated_event_state_lookup_eq in Hi.
      injection Hi as Hv. subst v.
      exact (Hback tid t eid e Ht Hget Href).
    + rewrite sem_set_updated_event_state_lookup_neq in Hi by exact Hneq.
      exact (Hback tid t i v Ht Hi Href).
  - eapply task_event_reference_closure_preserved_by_event_extension.
    + intros i [v Hi].
      change (exists v, inUsedEventStates
        (sem_set_updated_event_state (EventState ls) eid e cnt) i = Some v).
      destruct (Z.eq_dec i eid) as [Heq | Hneq].
      * subst i. eexists. apply sem_set_updated_event_state_lookup_eq.
      * exists v. rewrite sem_set_updated_event_state_lookup_neq by exact Hneq.
        exact Hi.
    + exact Hclosed.
Qed.
Lemma sem_set_mutex_lookup_iff__sem_set_all :
  forall evs eid e cnt i v,
    evs.(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    v.(eventType) = OS_EVENT_TYPE_MUTEX ->
    ((sem_set_updated_event_state evs eid e cnt).(inUsedEventStates) i = Some v
     <-> evs.(inUsedEventStates) i = Some v).
Proof.
  intros evs eid e cnt i v Hget Hsem Hmutex.
  destruct (Z.eq_dec i eid) as [Heq | Hneq].
  - subst i. rewrite sem_set_updated_event_state_lookup_eq, Hget.
    split; intro H; injection H as Hv; subst v; simpl in Hmutex;
      rewrite Hsem in Hmutex; discriminate.
  - rewrite sem_set_updated_event_state_lookup_neq by exact Hneq.
    reflexivity.
Qed.
