Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_task_wait_multi_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_remove_multi_spec.
Require Export Ucos2Verify.lib.sem Ucos2Verify.lib.mbox Ucos2Verify.lib.queue_core.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_full_inv.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Public OSEventPendMulti, original V2.93.01 joint configuration.
    These definitions are new work, not the old helper verification.
    No NoDup premise is imposed on the input: each occurrence is evaluated
    against the state resulting from the preceding occurrence.  ECB and QCB
    ownership stays in the single shared map, never in an input-list fold. *)
Definition event_pend_multi_supported_type (kind : OSEventType) : bool :=
  match kind with OS_EVENT_TYPE_SEM | OS_EVENT_TYPE_MBOX | OS_EVENT_TYPE_Q => true
  | _ => false end.

Record EventPendMultiMask := {
  event_pend_multi_sem_wait : bool;
  event_pend_multi_mbox_wait : bool;
  event_pend_multi_queue_wait : bool
}.
Definition event_pend_multi_empty_mask : EventPendMultiMask :=
  {| event_pend_multi_sem_wait := false; event_pend_multi_mbox_wait := false;
     event_pend_multi_queue_wait := false |}.
Definition event_pend_multi_mask_value (mask : EventPendMultiMask) : Z :=
  (if mask.(event_pend_multi_sem_wait) then 1 else 0) +
  (if mask.(event_pend_multi_mbox_wait) then 2 else 0) +
  (if mask.(event_pend_multi_queue_wait) then 4 else 0).
Definition event_pend_multi_add_wait (kind : OSEventType) (mask : EventPendMultiMask)
  : EventPendMultiMask :=
  {| event_pend_multi_sem_wait :=
       match kind with OS_EVENT_TYPE_SEM => true | _ => mask.(event_pend_multi_sem_wait) end;
     event_pend_multi_mbox_wait :=
       match kind with OS_EVENT_TYPE_MBOX => true | _ => mask.(event_pend_multi_mbox_wait) end;
     event_pend_multi_queue_wait :=
       match kind with OS_EVENT_TYPE_Q => true | _ => mask.(event_pend_multi_queue_wait) end |}.
Definition event_pend_multi_type_mask (kind : OSEventType) : Z :=
  match kind with OS_EVENT_TYPE_SEM => 1 | OS_EVENT_TYPE_MBOX => 2
  | OS_EVENT_TYPE_Q => 4 | _ => 0 end.

Lemma event_pend_multi_mask_in_range : forall mask,
  0 <= event_pend_multi_mask_value mask < 8.
Proof. intros [a b c]; destruct a, b, c; unfold event_pend_multi_mask_value; simpl; lia. Qed.
Lemma event_pend_multi_add_wait_value : forall kind mask,
  event_pend_multi_mask_value (event_pend_multi_add_wait kind mask) =
  Z.lor (event_pend_multi_mask_value mask) (event_pend_multi_type_mask kind).
Proof. intros [] [[] [] []]; reflexivity. Qed.

Inductive EventPendMultiProbe :=
| EventPendMultiTypeError
| EventPendMultiUnavailable (kind : OSEventType)
| EventPendMultiAcquired (message : addr) (after : Glob_EventAbstractState).

(** Missing primitive fields are malformed abstract states, not a fabricated
    C error branch.  The global representation establishes their consistency.
    An unused/free ECB has type UNUSED and takes the real type-error branch. *)
Definition event_pend_multi_probe (events : Glob_EventAbstractState) (eid : EventID)
  : option EventPendMultiProbe :=
  match events.(inUsedEventStates) eid with
  | None => Some EventPendMultiTypeError
  | Some e =>
      match e.(eventType) with
      | OS_EVENT_TYPE_SEM =>
          match e.(semFields) with
          | None => None
          | Some fields => if Z.ltb 0 fields.(semCount)
              then Some (EventPendMultiAcquired 0
                (update_event_field_raw events eid (sem_set_count e (fields.(semCount) - 1))))
              else Some (EventPendMultiUnavailable OS_EVENT_TYPE_SEM)
          end
      | OS_EVENT_TYPE_MBOX =>
          match e.(mboxFields) with
          | None => None
          | Some fields => if Z.eqb (mbox_message_ptr fields) 0
              then Some (EventPendMultiUnavailable OS_EVENT_TYPE_MBOX)
              else Some (EventPendMultiAcquired (mbox_message_ptr fields)
                (update_event_field_raw events eid (mbox_set_message e (mbox_message_from_ptr 0))))
          end
      | OS_EVENT_TYPE_Q =>
          match e.(queueFields) with
          | None => None
          | Some q => match queue_dequeue_front q with
              | None => Some (EventPendMultiUnavailable OS_EVENT_TYPE_Q)
              | Some (message, after) => match events.(publishedQueueBytes) q.(qID) with
                  | Some slots => Some (EventPendMultiAcquired message (queue_update events eid e after slots))
                  | None => None
                  end
              end
          end
      | _ => Some EventPendMultiTypeError
      end
  end.

Record EventPendMultiScan := {
  event_pend_multi_scan_events : Glob_EventAbstractState;
  event_pend_multi_scan_ready : list addr;
  event_pend_multi_scan_messages : list addr;
  event_pend_multi_scan_mask : EventPendMultiMask;
  event_pend_multi_scan_type_error : bool
}.

(** The count in C is INT16U; array cursors use the unbounded prefix length.
    In particular a prefix of length 65536 is not the blocking branch. *)
Definition event_pend_multi_return_count (prefix : list addr) : Z :=
  Zlength prefix mod 65536.
Definition event_pend_multi_any_ready (prefix : list addr) : bool :=
  match prefix with [] => false | _ => true end.

Fixpoint event_pend_multi_scan (sg : StableGlobVars) (ids : list EventID)
  (events : Glob_EventAbstractState) (mask : EventPendMultiMask)
  : option EventPendMultiScan :=
  match ids with
  | [] => Some {| event_pend_multi_scan_events := events;
      event_pend_multi_scan_ready := []; event_pend_multi_scan_messages := [];
      event_pend_multi_scan_mask := mask; event_pend_multi_scan_type_error := false |}
  | eid :: rest =>
      match event_pend_multi_probe events eid with
      | None => None
      | Some EventPendMultiTypeError => Some {| event_pend_multi_scan_events := events;
          event_pend_multi_scan_ready := []; event_pend_multi_scan_messages := [];
          event_pend_multi_scan_mask := mask; event_pend_multi_scan_type_error := true |}
      | Some (EventPendMultiUnavailable kind) =>
          event_pend_multi_scan sg rest events (event_pend_multi_add_wait kind mask)
      | Some (EventPendMultiAcquired message after) =>
          match event_pend_multi_scan sg rest after mask with
          | None => None
          | Some result => Some {| event_pend_multi_scan_events := result.(event_pend_multi_scan_events);
              event_pend_multi_scan_ready := event_addr sg eid :: result.(event_pend_multi_scan_ready);
              event_pend_multi_scan_messages := message :: result.(event_pend_multi_scan_messages);
              event_pend_multi_scan_mask := result.(event_pend_multi_scan_mask);
              event_pend_multi_scan_type_error := result.(event_pend_multi_scan_type_error) |}
          end
      end
  end.

Lemma event_pend_multi_scan_lengths : forall sg ids events mask result,
  event_pend_multi_scan sg ids events mask = Some result ->
  List.length result.(event_pend_multi_scan_ready) = List.length result.(event_pend_multi_scan_messages) /\
  (List.length result.(event_pend_multi_scan_ready) <= List.length ids)%nat.
Proof.
  intros sg ids; induction ids as [|eid rest IH]; intros events mask result Hscan;
    cbn [event_pend_multi_scan] in Hscan.
  - inversion Hscan; subst; simpl; auto.
  - destruct (event_pend_multi_probe events eid) as [[|kind|message after]|] eqn:Hprobe;
      try discriminate.
    + inversion Hscan; subst; simpl; auto with arith.
    + specialize (IH _ _ _ Hscan); simpl; lia.
    + destruct (event_pend_multi_scan sg rest after mask) as [tail|] eqn:Htail;
        try discriminate.
      inversion Hscan; subst; specialize (IH _ _ _ Htail); simpl; lia.
Qed.

Lemma event_pend_multi_scan_acquired_prefix : forall sg eid rest events mask message after tail,
  event_pend_multi_probe events eid = Some (EventPendMultiAcquired message after) ->
  event_pend_multi_scan sg rest after mask = Some tail ->
  exists result, event_pend_multi_scan sg (eid :: rest) events mask = Some result /\
    result.(event_pend_multi_scan_ready) = event_addr sg eid :: tail.(event_pend_multi_scan_ready) /\
    result.(event_pend_multi_scan_messages) = message :: tail.(event_pend_multi_scan_messages) /\
    result.(event_pend_multi_scan_type_error) = tail.(event_pend_multi_scan_type_error).
Proof. intros; cbn [event_pend_multi_scan]; rewrite H, H0; eexists; repeat split; reflexivity. Qed.

Lemma event_pend_multi_scan_error_stops : forall sg eid rest events mask,
  event_pend_multi_probe events eid = Some EventPendMultiTypeError ->
  event_pend_multi_scan sg (eid :: rest) events mask =
    Some {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := [];
      event_pend_multi_scan_messages := []; event_pend_multi_scan_mask := mask;
      event_pend_multi_scan_type_error := true |}.
Proof. intros; cbn [event_pend_multi_scan]; now rewrite H. Qed.

Lemma event_pend_multi_sem_decrement_preserves_validity : forall sg state eid e fields,
  UCOS2_full_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> e.(semFields) = Some fields -> 0 < fields.(semCount) ->
  UCOS2_full_state_inv sg (sem_count_update_state state eid e (fields.(semCount) - 1)).
Proof.
  intros sg state eid e fields Hvalid Hnode Htype Hfields Hcount.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e Hnode) as Hbefore; unfold event_payload_consistency in Hbefore.
  rewrite Htype, Hfields in Hbefore.
  eapply event_pend_multi_sem_count_update_preserves_validity; try eassumption.
  eapply sem_decrement_preserves_consistency; eassumption.
Qed.

Lemma event_pend_multi_mbox_take_preserves_validity : forall sg state eid e,
  UCOS2_full_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX ->
  UCOS2_full_state_inv sg (replace_EventS (update_event_field_raw state.(EventState) eid
    (mbox_set_message e (mbox_message_from_ptr 0))) state).
Proof.
  intros sg state eid e Hvalid Hnode Htype.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  eapply event_pend_multi_event_payload_update_preserves_validity; try eassumption; try reflexivity.
  pose proof Hevents as [_ [_ [_ [Hfields [_ [_ Hwait]]]]]].
  eapply event_update_preserves_in_range_with_wait; try eassumption.
  - reflexivity.
  - apply mbox_set_message_preserves_fields_consistency;
      [exact Htype|eapply Hfields; exact Hnode].
  - apply mbox_set_message_preserves_payload_consistency;
      [exact Htype|split; [exact I|reflexivity]].
  - unfold event_queue_id; simpl; rewrite Htype; reflexivity.
  - exact (Hwait eid e Hnode).
Qed.

Lemma event_pend_multi_probe_preserves_validity : forall sg state eid message after,
  UCOS2_full_state_inv sg state ->
  event_pend_multi_probe state.(EventState) eid = Some (EventPendMultiAcquired message after) ->
  UCOS2_full_state_inv sg (replace_EventS after state).
Proof.
  intros sg state eid message after Hvalid Hprobe; unfold event_pend_multi_probe in Hprobe.
  destruct (inUsedEventStates (EventState state) eid) as [e|] eqn:Hnode; try discriminate.
  destruct (eventType e) eqn:Htype; try discriminate.
  - destruct (semFields e) as [fields|] eqn:Hfields; try discriminate.
    destruct (Z.ltb 0 (semCount fields)) eqn:Hcount; try discriminate.
    inversion Hprobe; subst; apply Z.ltb_lt in Hcount.
    eapply event_pend_multi_sem_decrement_preserves_validity; eassumption.
  - destruct (mboxFields e) as [fields|] eqn:Hfields; try discriminate.
    destruct (Z.eqb (mbox_message_ptr fields) 0); try discriminate.
    inversion Hprobe; subst; eapply event_pend_multi_mbox_take_preserves_validity; eassumption.
  - destruct (queueFields e) as [q|] eqn:Hq; try discriminate.
    destruct (queue_dequeue_front q) as [[p next]|] eqn:Hstep; try discriminate.
    destruct (publishedQueueBytes (EventState state) (qID q)) as [slots|]; try discriminate.
    inversion Hprobe; subst; eapply event_pend_multi_queue_dequeue_preserves_validity; eassumption.
Qed.

Lemma event_pend_multi_replace_event_identity : forall state,
  replace_EventS state.(EventState) state = state.
Proof. intros []; reflexivity. Qed.
Lemma event_pend_multi_replace_event_last_write : forall state first last,
  replace_EventS last (replace_EventS first state) = replace_EventS last state.
Proof. intros []; reflexivity. Qed.

Lemma event_pend_multi_scan_preserves_validity : forall sg ids state mask result,
  UCOS2_full_state_inv sg state ->
  event_pend_multi_scan sg ids state.(EventState) mask = Some result ->
  UCOS2_full_state_inv sg (replace_EventS result.(event_pend_multi_scan_events) state).
Proof.
  intros sg ids; induction ids as [|eid rest IH]; intros state mask result Hvalid Hscan.
  - cbn [event_pend_multi_scan] in Hscan; inversion Hscan; subst.
    cbn [event_pend_multi_scan_events]; rewrite event_pend_multi_replace_event_identity; exact Hvalid.
  - cbn [event_pend_multi_scan] in Hscan.
    destruct (event_pend_multi_probe (EventState state) eid) as [[|kind|message after]|] eqn:Hprobe;
      try discriminate.
    + inversion Hscan; subst; cbn [event_pend_multi_scan_events].
      rewrite event_pend_multi_replace_event_identity; exact Hvalid.
    + eapply IH; eassumption.
    + destruct (event_pend_multi_scan sg rest after mask) as [tail|] eqn:Htail; try discriminate.
      inversion Hscan; subst; cbn [event_pend_multi_scan_events].
      pose proof (event_pend_multi_probe_preserves_validity sg state eid message after Hvalid Hprobe) as Hafter.
      specialize (IH (replace_EventS after state) mask tail Hafter Htail).
      rewrite event_pend_multi_replace_event_last_write in IH; exact IH.
Qed.

Lemma event_pend_multi_count_in_range : forall prefix,
  0 <= event_pend_multi_return_count prefix <= 65535.
Proof. intros; unfold event_pend_multi_return_count; pose proof (Z.mod_pos_bound (Zlength prefix) 65536); lia. Qed.
Lemma event_pend_multi_count_succ : forall prefix value,
  event_pend_multi_return_count (prefix ++ [value]) =
    (event_pend_multi_return_count prefix + 1) mod 65536.
Proof.
  intros; unfold event_pend_multi_return_count.
  rewrite Zlength_app, Zlength_cons, Zlength_nil; simpl.
  rewrite Z.add_mod_idemp_l by lia; reflexivity.
Qed.
Lemma event_pend_multi_any_ready_nonempty : forall prefix,
  event_pend_multi_any_ready prefix = false <-> prefix = [].
Proof. intros [|head tail]; simpl; split; intros; auto; discriminate. Qed.
Lemma event_pend_multi_wrapped_count_is_ready : forall prefix,
  Zlength prefix = 65536 ->
  event_pend_multi_return_count prefix = 0 /\ event_pend_multi_any_ready prefix = true.
Proof.
  intros prefix H; split.
  - unfold event_pend_multi_return_count; rewrite H; reflexivity.
  - destruct prefix; [rewrite Zlength_nil in H; lia|reflexivity].
Qed.

(** Arrays own initialized or uninitialized cells.  Null/error guards are
    ordered: ready/messages need no permissions on a path returning before
    their first dereference.  The error byte is always writable in this
    safety-critical-disabled configuration. *)
Definition EventPendMultiSlots := list (option addr).
Definition event_pend_multi_output_rep (base : addr) (slots : EventPendMultiSlots) : Assertion :=
  coq_prop (0 < base /\ base + 4 * Zlength slots <= 4294967296) &&
  PtrArray.mixed_full base (Zlength slots) slots.
Definition event_pend_multi_overlay (prefix : list addr) (old : EventPendMultiSlots)
  : EventPendMultiSlots := map (@Some addr) prefix ++ skipn (List.length prefix) old.
Definition event_pend_multi_ready_values (prefix : list addr) (old : EventPendMultiSlots)
  : EventPendMultiSlots := event_pend_multi_overlay (prefix ++ [0]) old.
Definition event_pend_multi_messages_values (prefix : list addr) (old : EventPendMultiSlots)
  : EventPendMultiSlots := event_pend_multi_overlay prefix old.
Definition event_pend_multi_scan_ready_values (prefix : list addr) (old : EventPendMultiSlots)
  : EventPendMultiSlots :=
  match prefix with [] => event_pend_multi_ready_values [] old | _ => event_pend_multi_overlay prefix old end.
Definition event_pend_multi_ready_flag (prefix : list addr) : Z :=
  if event_pend_multi_any_ready prefix then 1 else 0.

Inductive event_pend_multi_scan_history (sg : StableGlobVars) (ids : list EventID)
  (entry : Glob_EventAbstractState)
  : Z -> Glob_EventAbstractState -> list addr -> list addr -> EventPendMultiMask -> Prop :=
| event_pend_multi_history_start :
    event_pend_multi_scan_history sg ids entry 0 entry [] [] event_pend_multi_empty_mask
| event_pend_multi_history_unavailable : forall index events ready messages mask kind,
    event_pend_multi_scan_history sg ids entry index events ready messages mask ->
    0 <= index < Zlength ids ->
    event_pend_multi_probe events (Znth index ids 0) = Some (EventPendMultiUnavailable kind) ->
    event_pend_multi_scan_history sg ids entry (index + 1) events ready messages
      (event_pend_multi_add_wait kind mask)
| event_pend_multi_history_acquired : forall index events ready messages mask message after,
    event_pend_multi_scan_history sg ids entry index events ready messages mask ->
    0 <= index < Zlength ids ->
    event_pend_multi_probe events (Znth index ids 0) = Some (EventPendMultiAcquired message after) ->
    event_pend_multi_scan_history sg ids entry (index + 1) after
      (ready ++ [event_addr sg (Znth index ids 0)]) (messages ++ [message]) mask.

Lemma event_pend_multi_history_lengths : forall sg ids entry index events ready messages mask,
  event_pend_multi_scan_history sg ids entry index events ready messages mask ->
  0 <= index <= Zlength ids /\ Zlength ready = Zlength messages /\ Zlength ready <= index.
Proof.
  intros sg ids entry index events ready messages mask Hhistory; induction Hhistory.
  - repeat split; try reflexivity; pose proof (Zlength_nonneg ids); rewrite ?Zlength_nil; lia.
  - destruct IHHhistory as [Hindex [Hlen Hbound]]; repeat split; lia.
  - destruct IHHhistory as [Hindex [Hlen Hbound]].
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; repeat split; lia.
Qed.

Lemma event_pend_multi_overlay_length : forall prefix old,
  (List.length prefix <= List.length old)%nat ->
  List.length (event_pend_multi_overlay prefix old) = List.length old.
Proof. intros; unfold event_pend_multi_overlay; rewrite app_length, map_length, skipn_length; lia. Qed.
Lemma event_pend_multi_overlay_written_prefix : forall prefix old,
  firstn (List.length prefix) (event_pend_multi_overlay prefix old) = map (@Some addr) prefix.
Proof.
  intros; unfold event_pend_multi_overlay.
  rewrite firstn_app, firstn_all2 by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag; simpl; rewrite app_nil_r; reflexivity.
Qed.
Lemma event_pend_multi_overlay_unwritten_suffix : forall prefix old,
  skipn (List.length prefix) (event_pend_multi_overlay prefix old) = skipn (List.length prefix) old.
Proof.
  intros; unfold event_pend_multi_overlay.
  rewrite skipn_app, skipn_all2 by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag; reflexivity.
Qed.
Lemma event_pend_multi_ready_terminator : forall prefix old,
  nth (List.length prefix) (event_pend_multi_ready_values prefix old) None = Some 0.
Proof.
  intros; unfold event_pend_multi_ready_values, event_pend_multi_overlay.
  rewrite map_app; simpl.
  rewrite <- app_assoc; rewrite app_nth2 by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag; reflexivity.
Qed.

Definition event_pend_multi_input_arrays (pend ready messages : addr)
  (pointers : list addr) (old_ready old_messages : EventPendMultiSlots) : Assertion :=
  if Z.eq_dec pend 0 then emp else
  event_multi_array_rep pend pointers **
  (match pointers with [] => emp | _ =>
    if Z.eq_dec ready 0 then emp else
    if Z.eq_dec messages 0 then emp else
      coq_prop (Zlength pointers + 1 <= Zlength old_ready /\
                Zlength pointers <= Zlength old_messages) &&
      (event_pend_multi_output_rep ready old_ready **
       event_pend_multi_output_rep messages old_messages)
   end).

Definition event_pend_multi_guard_error (pend ready messages : addr) (pointers : list addr) : bool :=
  Z.eqb pend 0 || match pointers with [] => true | _ =>
    Z.eqb ready 0 || Z.eqb messages 0 end.

Definition event_pend_multi_pre (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (pend ready messages error : addr) (pointers : list addr)
  (old_ready old_messages : EventPendMultiSlots) (old_error : Z) : Assertion :=
  coq_prop (full_features_kernel_profile sg) &&
  (UCOS2_full_inv sg state ** event_pend_multi_input_arrays pend ready messages pointers old_ready old_messages **
   error # UChar |-> old_error).

Definition event_pend_multi_null_post (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (pend ready messages error : addr) (pointers : list addr)
  (old_ready old_messages : EventPendMultiSlots) (returned : Z) : Assertion :=
  coq_prop (event_pend_multi_guard_error pend ready messages pointers = true /\ returned = 0) &&
  (UCOS2_full_inv sg state ** event_pend_multi_input_arrays pend ready messages pointers old_ready old_messages **
   error # UChar |-> 4).

(** The public post is split by the actual source phases.  The remaining
    concurrent-call relation will be connected to the registered Save /
    scheduler producers, not supplied as a caller or platform axiom. *)
Definition event_pend_multi_scan_post (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (pend ready messages error : addr) (pointers : list addr)
  (old_ready old_messages : EventPendMultiSlots) (result : EventPendMultiScan)
  (returned : Z) : Assertion :=
  coq_prop (returned = event_pend_multi_return_count result.(event_pend_multi_scan_ready)) &&
  (UCOS2_raw_rep sg (replace_EventS result.(event_pend_multi_scan_events) state) **
   event_multi_array_rep pend pointers **
   event_pend_multi_output_rep ready
     (event_pend_multi_ready_values result.(event_pend_multi_scan_ready) old_ready) **
   event_pend_multi_output_rep messages
     (event_pend_multi_messages_values result.(event_pend_multi_scan_messages) old_messages) **
   error # UChar |-> (if result.(event_pend_multi_scan_type_error) then 1 else 0)).

Lemma event_pend_multi_cleanup_observations : forall t,
  encode_task_status (stat (task_multi_cleanup t)) = 0 /\
  statPend (task_multi_cleanup t) = PendOK /\
  tcbEventMultiPtr (task_multi_cleanup t) = 0 /\
  eventMultiRdy (task_multi_cleanup t) = None /\
  msg (task_multi_cleanup t) = None /\
  dly (task_multi_cleanup t) = dly t /\
  eventPtr (task_multi_cleanup t) = eventPtr t.
Proof. intros; repeat split; reflexivity. Qed.

(** Prefix composition is valid even when the same ECB occurs in both
    lists.  The suffix starts from the prefix's actual updated Event map. *)
Definition event_pend_multi_scan_append (prefix suffix : EventPendMultiScan) : EventPendMultiScan :=
  {| event_pend_multi_scan_events := suffix.(event_pend_multi_scan_events);
     event_pend_multi_scan_ready := prefix.(event_pend_multi_scan_ready) ++ suffix.(event_pend_multi_scan_ready);
     event_pend_multi_scan_messages := prefix.(event_pend_multi_scan_messages) ++ suffix.(event_pend_multi_scan_messages);
     event_pend_multi_scan_mask := suffix.(event_pend_multi_scan_mask);
     event_pend_multi_scan_type_error := suffix.(event_pend_multi_scan_type_error) |}.

Lemma event_pend_multi_scan_concat : forall sg first last events mask prefix suffix,
  event_pend_multi_scan sg first events mask = Some prefix ->
  prefix.(event_pend_multi_scan_type_error) = false ->
  event_pend_multi_scan sg last prefix.(event_pend_multi_scan_events)
    prefix.(event_pend_multi_scan_mask) = Some suffix ->
  event_pend_multi_scan sg (first ++ last) events mask = Some (event_pend_multi_scan_append prefix suffix).
Proof.
  intros sg first; induction first as [|eid rest IH]; intros last events mask prefix suffix Hfirst Hvalid Hlast.
  - cbn [event_pend_multi_scan] in Hfirst; inversion Hfirst; subst prefix.
    cbn [event_pend_multi_scan_append] in *; simpl in *.
    destruct suffix; exact Hlast.
  - cbn [List.app event_pend_multi_scan] in Hfirst |- *.
    destruct (event_pend_multi_probe events eid) as [[|kind|message after]|] eqn:Hprobe; try discriminate.
    + inversion Hfirst; subst; discriminate.
    + eapply IH; eassumption.
    + destruct (event_pend_multi_scan sg rest after mask) as [tail|] eqn:Htail; try discriminate.
      inversion Hfirst; subst prefix.
      cbn [event_pend_multi_scan_type_error event_pend_multi_scan_events event_pend_multi_scan_mask] in *.
      rewrite (IH last after mask tail suffix Htail Hvalid Hlast); reflexivity.
Qed.

Lemma event_pend_multi_scan_error_ignores_suffix : forall sg first last events mask result,
  event_pend_multi_scan sg first events mask = Some result ->
  result.(event_pend_multi_scan_type_error) = true ->
  event_pend_multi_scan sg (first ++ last) events mask = Some result.
Proof.
  intros sg first; induction first as [|eid rest IH]; intros last events mask result Hscan Herr.
  - cbn [event_pend_multi_scan] in Hscan; inversion Hscan; subst; discriminate.
  - cbn [List.app event_pend_multi_scan] in Hscan |- *.
    destruct (event_pend_multi_probe events eid) as [[|kind|message after]|] eqn:Hprobe; try discriminate.
    + exact Hscan.
    + eapply IH; eassumption.
    + destruct (event_pend_multi_scan sg rest after mask) as [tail|] eqn:Htail; try discriminate.
      inversion Hscan; subst result; cbn [event_pend_multi_scan_type_error] in Herr.
      rewrite (IH last after mask tail Htail Herr); reflexivity.
Qed.

Lemma event_pend_multi_scan_without_ready_keeps_events : forall sg ids events mask result,
  event_pend_multi_scan sg ids events mask = Some result ->
  result.(event_pend_multi_scan_ready) = [] -> result.(event_pend_multi_scan_events) = events.
Proof.
  intros sg ids; induction ids as [|eid rest IH]; intros events mask result Hscan Hempty.
  - cbn [event_pend_multi_scan] in Hscan; inversion Hscan; reflexivity.
  - cbn [event_pend_multi_scan] in Hscan.
    destruct (event_pend_multi_probe events eid) as [[|kind|message after]|] eqn:Hprobe; try discriminate.
    + inversion Hscan; reflexivity.
    + eapply IH; eassumption.
    + destruct (event_pend_multi_scan sg rest after mask); inversion Hscan; subst; discriminate.
Qed.

Lemma event_pend_multi_duplicate_acquisitions : forall sg eid events mask first after second final,
  event_pend_multi_probe events eid = Some (EventPendMultiAcquired first after) ->
  event_pend_multi_probe after eid = Some (EventPendMultiAcquired second final) ->
  event_pend_multi_scan sg [eid; eid] events mask = Some
    {| event_pend_multi_scan_events := final;
       event_pend_multi_scan_ready := [event_addr sg eid; event_addr sg eid];
       event_pend_multi_scan_messages := [first; second];
       event_pend_multi_scan_mask := mask; event_pend_multi_scan_type_error := false |}.
Proof. intros; cbn [event_pend_multi_scan]; rewrite H, H0; reflexivity. Qed.

Lemma event_pend_multi_acquisition_before_type_error : forall sg eid bad rest events mask message after,
  event_pend_multi_probe events eid = Some (EventPendMultiAcquired message after) ->
  event_pend_multi_probe after bad = Some EventPendMultiTypeError ->
  event_pend_multi_scan sg (eid :: bad :: rest) events mask = Some
    {| event_pend_multi_scan_events := after; event_pend_multi_scan_ready := [event_addr sg eid];
       event_pend_multi_scan_messages := [message]; event_pend_multi_scan_mask := mask;
       event_pend_multi_scan_type_error := true |}.
Proof. intros; cbn [event_pend_multi_scan]; rewrite H, H0; reflexivity. Qed.

Lemma event_pend_multi_null_guard_cases : forall pend ready messages pointers,
  pend = 0 \/ pointers = [] \/ ready = 0 \/ messages = 0 ->
  event_pend_multi_guard_error pend ready messages pointers = true.
Proof.
  intros pend ready messages pointers H; unfold event_pend_multi_guard_error.
  destruct H as [H|[H|[H|H]]]; subst.
  - reflexivity.
  - apply Bool.orb_true_r.
  - destruct pointers; simpl; rewrite ?Z.eqb_refl, ?Bool.orb_true_r; reflexivity.
  - destruct pointers; simpl; rewrite ?Z.eqb_refl, ?Bool.orb_true_r; reflexivity.
Qed.

Lemma event_pend_multi_nonnull_guard_cases : forall pend ready messages pointers,
  event_pend_multi_guard_error pend ready messages pointers = false <->
  pend <> 0 /\ pointers <> [] /\ ready <> 0 /\ messages <> 0.
Proof.
  intros; unfold event_pend_multi_guard_error; destruct pointers as [|head tail]; simpl.
  - rewrite Bool.orb_true_r; split; [discriminate|tauto].
  - rewrite !Bool.orb_false_iff, !Z.eqb_neq; split; intros; intuition discriminate.
Qed.

Lemma event_pend_multi_nonnull_guard_length : forall pend ready messages pointers,
  event_pend_multi_guard_error pend ready messages pointers = false <->
  pend <> 0 /\ 0 < Zlength pointers /\ ready <> 0 /\ messages <> 0.
Proof.
  intros; rewrite event_pend_multi_nonnull_guard_cases.
  destruct pointers as [|head tail].
  - rewrite Zlength_nil; intuition lia.
  - assert (Hnonnull : head :: tail <> []) by discriminate.
    assert (Hpositive : 0 < Zlength (head :: tail)).
    { rewrite Zlength_cons; pose proof (Zlength_nonneg tail); lia. }
    tauto.
Qed.

Lemma event_pend_multi_ready_output_length : forall prefix old,
  (List.length prefix + 1 <= List.length old)%nat ->
  List.length (event_pend_multi_ready_values prefix old) = List.length old /\
  nth (List.length prefix) (event_pend_multi_ready_values prefix old) None = Some 0 /\
  skipn (List.length prefix + 1) (event_pend_multi_ready_values prefix old) =
    skipn (List.length prefix + 1) old.
Proof.
  intros prefix old Hcapacity; split.
  - apply event_pend_multi_overlay_length; rewrite app_length; simpl; exact Hcapacity.
  - split; [apply event_pend_multi_ready_terminator|].
    assert (Hlen : List.length (prefix ++ [0]) = (List.length prefix + 1)%nat)
      by (rewrite app_length; reflexivity).
    unfold event_pend_multi_ready_values; rewrite <- Hlen.
    apply event_pend_multi_overlay_unwritten_suffix.
Qed.

(** The loop history and the recursive public result describe the same
    ordered prefix, including repeated Event identifiers. *)
Lemma event_pend_multi_firstn_step : forall (ids : list EventID) index,
  (index < List.length ids)%nat ->
  firstn (S index) ids = firstn index ids ++ [nth index ids 0].
Proof.
  induction ids as [|eid ids IH]; intros [|index] H; cbn in *; try lia; try reflexivity.
  rewrite IH by lia; reflexivity.
Qed.

Lemma event_pend_multi_prefix_step : forall ids index,
  0 <= index < Zlength ids ->
  firstn (Z.to_nat (index + 1)) ids =
    firstn (Z.to_nat index) ids ++ [Znth index ids 0].
Proof.
  intros ids index Hrange; unfold Znth.
  rewrite Z.add_1_r, Z2Nat.inj_succ by exact (proj1 Hrange).
  apply event_pend_multi_firstn_step.
  rewrite Zlength_correct in Hrange; destruct Hrange as [Hnonnegative Hbound].
  pose proof (proj1 (Z2Nat.inj_lt index (Z.of_nat (List.length ids))
    Hnonnegative (Nat2Z.is_nonneg _)) Hbound) as Hnat.
  rewrite Nat2Z.id in Hnat; exact Hnat.
Qed.

Lemma event_pend_multi_history_scan : forall sg ids entry index events ready messages mask,
  event_pend_multi_scan_history sg ids entry index events ready messages mask ->
  event_pend_multi_scan sg (firstn (Z.to_nat index) ids) entry event_pend_multi_empty_mask =
    Some {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := ready;
      event_pend_multi_scan_messages := messages; event_pend_multi_scan_mask := mask;
      event_pend_multi_scan_type_error := false |}.
Proof.
  intros sg ids entry index events ready messages mask Hhistory; induction Hhistory.
  - reflexivity.
  - rewrite event_pend_multi_prefix_step by exact H.
    assert (Htail : event_pend_multi_scan sg [Znth index ids 0] events mask =
      Some {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := [];
        event_pend_multi_scan_messages := []; event_pend_multi_scan_mask := event_pend_multi_add_wait kind mask;
        event_pend_multi_scan_type_error := false |}).
    { cbn [event_pend_multi_scan]; rewrite H0; reflexivity. }
    pose proof (event_pend_multi_scan_concat sg (firstn (Z.to_nat index) ids) [Znth index ids 0]
      entry event_pend_multi_empty_mask _ _ IHHhistory eq_refl Htail) as Hscan.
    unfold event_pend_multi_scan_append in Hscan.
    cbn [event_pend_multi_scan_events event_pend_multi_scan_ready
      event_pend_multi_scan_messages event_pend_multi_scan_mask event_pend_multi_scan_type_error] in Hscan.
    rewrite ?app_nil_r in Hscan; exact Hscan.
  - rewrite event_pend_multi_prefix_step by exact H.
    assert (Htail : event_pend_multi_scan sg [Znth index ids 0] events mask =
      Some {| event_pend_multi_scan_events := after;
        event_pend_multi_scan_ready := [event_addr sg (Znth index ids 0)];
        event_pend_multi_scan_messages := [message]; event_pend_multi_scan_mask := mask;
        event_pend_multi_scan_type_error := false |}).
    { cbn [event_pend_multi_scan]; rewrite H0; reflexivity. }
    exact (event_pend_multi_scan_concat sg (firstn (Z.to_nat index) ids) [Znth index ids 0]
      entry event_pend_multi_empty_mask _ _ IHHhistory eq_refl Htail).
Qed.

Lemma event_pend_multi_history_finished : forall sg ids entry events ready messages mask,
  event_pend_multi_scan_history sg ids entry (Zlength ids) events ready messages mask ->
  event_pend_multi_scan sg ids entry event_pend_multi_empty_mask =
    Some {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := ready;
      event_pend_multi_scan_messages := messages; event_pend_multi_scan_mask := mask;
      event_pend_multi_scan_type_error := false |}.
Proof.
  intros sg ids entry events ready messages mask Hhistory.
  pose proof (event_pend_multi_history_scan sg ids entry (Zlength ids) events ready messages mask Hhistory) as Hscan.
  rewrite Zlength_correct, Nat2Z.id, firstn_all in Hscan; exact Hscan.
Qed.

Lemma event_pend_multi_history_type_error : forall sg ids entry index events ready messages mask,
  event_pend_multi_scan_history sg ids entry index events ready messages mask ->
  0 <= index < Zlength ids ->
  event_pend_multi_probe events (Znth index ids 0) = Some EventPendMultiTypeError ->
  event_pend_multi_scan sg ids entry event_pend_multi_empty_mask =
    Some {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := ready;
      event_pend_multi_scan_messages := messages; event_pend_multi_scan_mask := mask;
      event_pend_multi_scan_type_error := true |}.
Proof.
  intros sg ids entry index events ready messages mask Hhistory Hrange Hprobe.
  pose proof (event_pend_multi_history_scan sg ids entry index events ready messages mask Hhistory) as Hprefix.
  assert (Hsingle : event_pend_multi_scan sg [Znth index ids 0] events mask =
    Some {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := [];
      event_pend_multi_scan_messages := []; event_pend_multi_scan_mask := mask;
      event_pend_multi_scan_type_error := true |}).
  { cbn [event_pend_multi_scan]; rewrite Hprobe; reflexivity. }
  pose proof (event_pend_multi_scan_concat sg (firstn (Z.to_nat index) ids) [Znth index ids 0]
    entry event_pend_multi_empty_mask _ _ Hprefix eq_refl Hsingle) as Hscan.
  unfold event_pend_multi_scan_append in Hscan.
  cbn [event_pend_multi_scan_events event_pend_multi_scan_ready event_pend_multi_scan_messages
    event_pend_multi_scan_mask event_pend_multi_scan_type_error] in Hscan.
  rewrite !app_nil_r, <- event_pend_multi_prefix_step in Hscan by exact Hrange.
  pose proof (event_pend_multi_scan_error_ignores_suffix sg
    (firstn (Z.to_nat (index + 1)) ids) (skipn (Z.to_nat (index + 1)) ids)
    entry event_pend_multi_empty_mask _ Hscan eq_refl) as Hcomplete.
  rewrite firstn_skipn in Hcomplete; exact Hcomplete.
Qed.
