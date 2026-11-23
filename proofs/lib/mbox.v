Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms Feq ListLib VMap.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Import ListNotations.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared mailbox message operations. An OS_EVENT owns the pointer cell,
    never the pointed-to application bytes. In particular a broadcast of
    one pointer cannot duplicate exclusive ownership of its contents.
    These local operations do not abstract away Task/Sched wakeup, private
    ECB allocation, entry checks, or the lifetime of a blocked invocation. *)
Definition mbox_message_ptr (m : MboxFields) : addr :=
  match m.(mboxMsg) with None => 0 | Some p => p end.

Definition mbox_message_from_ptr (p : addr) : MboxFields :=
  {| mboxMsg := if Z.eqb p 0 then None else Some p |}.

Lemma mbox_message_ptr_from_ptr : forall p,
  mbox_message_ptr (mbox_message_from_ptr p) = p.
Proof.
  intros p; unfold mbox_message_ptr, mbox_message_from_ptr; simpl.
  destruct (Z.eqb p 0) eqn:H; [apply Z.eqb_eq in H; congruence|reflexivity].
Qed.

Lemma mbox_message_from_ptr_nonzero : forall p,
  p <> 0 -> mboxMsg (mbox_message_from_ptr p) = Some p.
Proof.
  intros p Hp; unfold mbox_message_from_ptr; simpl.
  destruct (Z.eqb p 0) eqn:H; [apply Z.eqb_eq in H; contradiction|reflexivity].
Qed.

Definition mbox_set_message (e : OSEventAbstractState) (m : MboxFields)
  : OSEventAbstractState :=
  {| eventGeneration := e.(eventGeneration);
     eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
     eventType := e.(eventType); mutexFields := e.(mutexFields); semFields := e.(semFields);
     mboxFields := Some m; queueFields := e.(queueFields); waitList := e.(waitList) |}.

Lemma mbox_set_message_same : forall e m,
  e.(mboxFields) = Some m -> mbox_set_message e m = e.
Proof. intros e m H; destruct e; simpl in H; subst; reflexivity. Qed.

Lemma mbox_set_message_last_write : forall e m1 m2,
  mbox_set_message (mbox_set_message e m1) m2 = mbox_set_message e m2.
Proof. reflexivity. Qed.

Lemma mbox_set_message_preserves_fields_consistency : forall e m,
  e.(eventType) = OS_EVENT_TYPE_MBOX -> event_fields_consistency e ->
  event_fields_consistency (mbox_set_message e m).
Proof.
  intros e m Hty Hfields; unfold event_fields_consistency in *;
    simpl; rewrite Hty in *; intuition discriminate.
Qed.

Lemma mbox_set_message_preserves_payload_consistency : forall sg e m,
  e.(eventType) = OS_EVENT_TYPE_MBOX -> mbox_fields_consistency e.(waitList) m ->
  event_payload_consistency sg (mbox_set_message e m).
Proof.
  intros sg e m Hty Hm; unfold event_payload_consistency; simpl; rewrite Hty; exact Hm.
Qed.

Lemma mbox_set_message_preserves_event_in_range : forall sg tasks events eid e m,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX -> mbox_fields_consistency e.(waitList) m ->
  event_in_range sg tasks (update_event_field_raw events eid (mbox_set_message e m)).
Proof.
  intros sg tasks events eid e m Hvalid Hget Hty Hm.
  pose proof Hvalid as [Hp [Hfree [Hidentity [Hfields [Hpayload [Hq Hwait]]]]]].
  apply event_update_preserves_in_range with (old := e).
  - exact Hvalid.
  - exact Hget.
  - reflexivity.
  - apply mbox_set_message_preserves_fields_consistency; [exact Hty|eapply Hfields; eauto].
  - apply mbox_set_message_preserves_payload_consistency; assumption.
  - unfold event_queue_id; simpl; rewrite Hty; reflexivity.
  - exact (Hwait eid e Hget).
Qed.

(** Accept always writes NULL, including the already-empty case; the same
    message-cell operation is used by the immediate-success branch of Pend. *)
Definition mbox_take (m : MboxFields) : addr * MboxFields :=
  (mbox_message_ptr m, {| mboxMsg := None |}).

Lemma mbox_take_returns_previous_message : forall m,
  fst (mbox_take m) = mbox_message_ptr m /\ mboxMsg (snd (mbox_take m)) = None.
Proof. intros m; split; reflexivity. Qed.

Lemma mbox_take_preserves_consistency : forall wl m,
  mbox_fields_consistency wl (snd (mbox_take m)).
Proof. intros wl m; split; [exact I|reflexivity]. Qed.

Lemma mbox_take_preserves_event_in_range : forall sg tasks events eid e m,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX ->
  event_in_range sg tasks
    (update_event_field_raw events eid (mbox_set_message e (snd (mbox_take m)))).
Proof.
  intros; eapply mbox_set_message_preserves_event_in_range; eauto.
  apply mbox_take_preserves_consistency.
Qed.

(** Store is only the no-waiter branch shared by Post and PostOpt. Its
    NULL rejection assumes argument checking, as in the selected profile;
    when that macro is disabled, non-NULL is an explicit API precondition. *)
Definition mbox_store (m : MboxFields) (p : addr) : OSErrCode * MboxFields :=
  if Z.eqb p 0 then (OS_ERR_POST_NULL_PTR, m)
  else match m.(mboxMsg) with
       | Some _ => (OS_ERR_MBOX_FULL, m)
       | None => (OS_ERR_NONE, {| mboxMsg := Some p |})
       end.

Lemma mbox_store_null : forall m, mbox_store m 0 = (OS_ERR_POST_NULL_PTR, m).
Proof. reflexivity. Qed.

Lemma mbox_store_full : forall m old p,
  m.(mboxMsg) = Some old -> p <> 0 -> mbox_store m p = (OS_ERR_MBOX_FULL, m).
Proof.
  intros m old p Hm Hp; unfold mbox_store; rewrite Hm.
  destruct (Z.eqb p 0) eqn:H; [apply Z.eqb_eq in H; contradiction|reflexivity].
Qed.

Lemma mbox_store_empty : forall m p,
  m.(mboxMsg) = None -> p <> 0 ->
  mbox_store m p = (OS_ERR_NONE, {| mboxMsg := Some p |}).
Proof.
  intros m p Hm Hp; unfold mbox_store; rewrite Hm.
  destruct (Z.eqb p 0) eqn:H; [apply Z.eqb_eq in H; contradiction|reflexivity].
Qed.

Lemma mbox_store_failure_unchanged : forall m p err after,
  mbox_store m p = (err, after) -> err <> OS_ERR_NONE -> after = m.
Proof.
  intros m p err after H Herror; unfold mbox_store in H.
  destruct (Z.eqb p 0); [inversion H; reflexivity|].
  destruct (mboxMsg m); inversion H; congruence.
Qed.

Lemma mbox_store_preserves_consistency : forall m p,
  mbox_fields_consistency [] m -> mbox_fields_consistency [] (snd (mbox_store m p)).
Proof.
  intros m p Hm; unfold mbox_store.
  destruct (Z.eqb p 0) eqn:Hp; [exact Hm|].
  destruct (mboxMsg m); [exact Hm|].
  split; [apply Z.eqb_neq in Hp; exact Hp|intros H; contradiction].
Qed.

Lemma mbox_store_preserves_event_in_range : forall sg tasks events eid e m p,
  event_in_range sg tasks events -> events.(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX -> e.(mboxFields) = Some m -> e.(waitList) = [] ->
  event_in_range sg tasks
    (update_event_field_raw events eid (mbox_set_message e (snd (mbox_store m p)))).
Proof.
  intros sg tasks events eid e m p Hvalid Hget Hty Hm Hwait.
  eapply mbox_set_message_preserves_event_in_range; try eassumption.
  rewrite Hwait; apply mbox_store_preserves_consistency.
  destruct Hvalid as [_ [_ [_ [_ [Hpayload _]]]]].
  specialize (Hpayload eid e Hget); unfold event_payload_consistency in Hpayload.
  rewrite Hty, Hm, Hwait in Hpayload; exact Hpayload.
Qed.

Definition mbox_rep_no_message (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks e) EventPtrField.

Lemma mbox_rep_split_message : forall sg tasks eid e m,
  e.(eventType) = OS_EVENT_TYPE_MBOX -> e.(mboxFields) = Some m ->
  used_event_rep sg tasks eid e |--
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr m **
  mbox_rep_no_message sg tasks eid e.
Proof.
  intros sg tasks eid e m Hty Hm.
  unfold used_event_rep, mbox_rep_no_message.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks e) EventPtrField ltac:(simpl; tauto)).
  cbn [event_image event_cell event_field_offset].
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value; rewrite Hty, Hm.
  unfold OSEventPtr_off, mbox_message_ptr; simpl; entailer!.
Qed.

Lemma mbox_rep_merge_updated_message : forall sg tasks eid e m,
  e.(eventType) = OS_EVENT_TYPE_MBOX ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr m **
  mbox_rep_no_message sg tasks eid e |--
  used_event_rep sg tasks eid (mbox_set_message e m).
Proof.
  intros sg tasks eid e m Hty.
  assert (Himage : event_image sg tasks (mbox_set_message e m) =
    event_write (event_image sg tasks e) EventPtrField (Some (mbox_message_ptr m))).
  { apply functional_extensionality; intros []; cbn [event_image event_write
      field_update mbox_set_message]; try reflexivity.
    unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value;
      simpl; rewrite Hty; reflexivity. }
  unfold used_event_rep, mbox_rep_no_message; rewrite Himage.
  apply (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks e) EventPtrField (Some (mbox_message_ptr m)) ltac:(simpl; tauto)).
Qed.
