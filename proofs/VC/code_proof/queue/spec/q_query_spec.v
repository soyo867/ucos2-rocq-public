Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** OSQQuery, V2.93.01 os_q.c:876--919.  Argument checks precede
    the unconditional type read.  This API has no safety hook, ISR/lock
    rejection, trace call or scheduler call.  The observation below is
    taken inside Save/Restore, not after the caller resumes unmasked. *)
Definition q_query_argument_error (sg : StableGlobVars) (pevent pdata : addr)
  : option OSErrCode :=
  if sg.(osKernelConfig).(cfgArgumentChecks) then
    if Z.eqb pevent 0 then Some OS_ERR_PEVENT_NULL
    else if Z.eqb pdata 0 then Some OS_ERR_PDATA_NULL else None
  else None.

Definition q_query_type_error (type_byte : Z) : option OSErrCode :=
  if Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_Q)
  then None else Some OS_ERR_EVENT_TYPE.

(** Caller-visible OS_Q_DATA fields, not another kernel Queue state.
    The current global profile uses eight UChar wait rows.  Wider
    OS_PRIO configurations require their own Event encoding/layout. *)
Record QueueQuerySnapshot := {
  q_query_message : addr;
  q_query_entries : Z;
  q_query_capacity : Z;
  q_query_wait_rows : list Z;
  q_query_wait_group : Z
}.

Definition queue_query_snapshot (tasks : Glob_TaskAbstractState)
  (e : OSEventAbstractState) (q : QueueFields) (message : addr) : QueueQuerySnapshot :=
  {| q_query_message := message;
     q_query_entries := queue_entries q;
     q_query_capacity := q.(qSize);
     q_query_wait_rows := encode_event_wait_tbl_values_or e tasks;
     q_query_wait_group := encode_event_wait_grp e.(waitList) tasks |}.

(** Only the nonempty arm reads a ring slot.  A stored NULL is a valid
    message and is not conflated with an unspecified/uninitialized slot.
    Neither arm advances Out, changes Entries, nor clears buffer bytes. *)
Definition q_query_critical (sg : StableGlobVars) (eid : EventID)
  : program UCOS2_Verify_State QueueQuerySnapshot :=
  fun s snapshot after => after = s /\ exists e q,
    s.(EventState).(inUsedEventStates) eid = Some e /\ e.(queueFields) = Some q /\
    if Z.ltb 0 (queue_entries q) then
      exists slots message,
        s.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
        Znth q.(qOutIndex) slots None = Some message /\
        snapshot = queue_query_snapshot s.(TskState) e q message
    else snapshot = queue_query_snapshot s.(TskState) e q 0.

Lemma q_query_critical_exists : forall sg s eid e q,
  UCOS2_state_inv sg s -> queue_published_storage_binding s.(EventState) ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  e.(queueFields) = Some q -> exists snapshot, q_query_critical sg eid s snapshot s.
Proof.
  intros sg s eid e q Hvalid Hbinding He Htype Hq.
  destruct (Z.ltb 0 (queue_entries q)) eqn:Hcount.
  - destruct (proj1 Hbinding eid e q He Hq) as [_ [slots [Hslots Hmodel]]].
    assert (Hpop : exists message next, queue_dequeue_front q = Some (message, next)).
    { unfold queue_dequeue_front; destruct q.(qMessages) as [|message rest] eqn:Hmessages; [|eauto].
      unfold queue_entries in Hcount; rewrite Hmessages, Zlength_nil in Hcount; discriminate. }
    destruct Hpop as [message [next Hpop]].
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
    pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
    rewrite Htype, Hq in Hqueue.
    exists (queue_query_snapshot s.(TskState) e q message); split; [reflexivity|].
    exists e, q; split; [exact He|]; split; [exact Hq|]; rewrite Hcount.
    exists slots, message; split; [exact Hslots|]; split; [|reflexivity].
    eapply queue_dequeue_front_head_slot; eauto.
  - exists (queue_query_snapshot s.(TskState) e q 0); split; [reflexivity|].
    exists e, q; split; [exact He|]; split; [exact Hq|]; rewrite Hcount; reflexivity.
Qed.

Lemma q_query_critical_deterministic : forall sg eid s r1 s1 r2 s2,
  q_query_critical sg eid s r1 s1 -> q_query_critical sg eid s r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid s r1 s1 r2 s2 [-> [e1 [q1 [He1 [Hq1 Hfirst]]]]]
    [-> [e2 [q2 [He2 [Hq2 Hsecond]]]]].
  assert (e2 = e1) by congruence; subst e2.
  assert (q2 = q1) by congruence; subst q2; split; [|reflexivity].
  destruct (Z.ltb 0 (queue_entries q1)).
  - destruct Hfirst as [slots1 [m1 [Hslots1 [Hm1 ->]]]].
    destruct Hsecond as [slots2 [m2 [Hslots2 [Hm2 ->]]]].
    assert (slots2 = slots1) by congruence; subst slots2.
    assert (m2 = m1) by congruence; subst m2; reflexivity.
  - congruence.
Qed.

Lemma q_query_critical_kernel_state_eq : forall sg eid s snapshot after,
  q_query_critical sg eid s snapshot after -> after = s.
Proof. intros sg eid s snapshot after [Hsame _]; exact Hsame. Qed.

Lemma q_query_critical_preserves_validity : forall sg eid s snapshot after,
  UCOS2_state_inv sg s -> q_query_critical sg eid s snapshot after ->
  UCOS2_state_inv sg after.
Proof. intros sg eid s snapshot after Hvalid [-> _]; exact Hvalid. Qed.

Lemma q_query_critical_queue_observation : forall sg eid s e q snapshot after,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(queueFields) = Some q ->
  q_query_critical sg eid s snapshot after ->
  snapshot.(q_query_entries) = queue_entries q /\
  snapshot.(q_query_capacity) = q.(qSize) /\
  snapshot.(q_query_wait_rows) = encode_event_wait_tbl_values_or e s.(TskState) /\
  snapshot.(q_query_wait_group) = encode_event_wait_grp e.(waitList) s.(TskState) /\
  (if Z.ltb 0 (queue_entries q) then
     exists slots, s.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
       Znth q.(qOutIndex) slots None = Some snapshot.(q_query_message)
   else snapshot.(q_query_message) = 0).
Proof.
  intros sg eid s e q snapshot after He Hq [_ [node [before [Hnode [Hbefore Hstep]]]]].
  assert (node = e) by congruence; subst node.
  assert (before = q) by congruence; subst before.
  destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [slots [message [Hslots [Hmessage ->]]]].
    repeat split; try reflexivity; exists slots; split; assumption.
  - subst snapshot; repeat split; reflexivity.
Qed.

Lemma q_query_snapshot_wait_rows_length : forall tasks e q message,
  Zlength (queue_query_snapshot tasks e q message).(q_query_wait_rows) = 8.
Proof. intros; reflexivity. Qed.

(** Exactly the written fields of the selected OS_Q_DATA layout.
    Padding and any other caller-owned bytes remain a separate frame.
    These symbolic field addresses must be bound by the actual QCP C
    declaration; no unproved numeric struct offsets are assumed here.
    The source writes group, then the typed row-copy loop, then message,
    count and size.  Kernel ownership must be separated from this output. *)
Definition q_query_output_fields_rep (base : addr) (snapshot : QueueQuerySnapshot) : Assertion :=
  (&(base # "os_q_data" ->ₛ "OSEventGrp")) # UChar |-> snapshot.(q_query_wait_group) **
  UCharArray.full (&(base # "os_q_data" ->ₛ "OSEventTbl")) 8 snapshot.(q_query_wait_rows) **
  (&(base # "os_q_data" ->ₛ "OSMsg")) # Ptr |-> snapshot.(q_query_message) **
  (&(base # "os_q_data" ->ₛ "OSNMsgs")) # UShort |-> snapshot.(q_query_entries) **
  (&(base # "os_q_data" ->ₛ "OSQSize")) # UShort |-> snapshot.(q_query_capacity).

(** Loop state reuses [copy_prefix_list] and QCP's mixed typed arrays:
    rows already copied are initialized, the untouched suffix keeps its
    exact old values, including unspecified bytes. *)
Definition q_query_wait_copy_rep (output : addr) (rows : list Z)
  (initial : list (option Z)) (i : Z) : Assertion :=
  UCharArray.mixed_full output (Zlength rows)
    (copy_prefix_list (map (@Some Z) rows) initial i).

Lemma q_query_wait_copy_initial : forall output rows initial,
  q_query_wait_copy_rep output rows initial 0 =
  UCharArray.mixed_full output (Zlength rows) initial.
Proof. intros; reflexivity. Qed.

Lemma q_query_wait_row_initialized : forall rows i,
  0 <= i < Zlength rows ->
  Znth i (map (@Some Z) rows) None = Some (Znth i rows 0).
Proof.
  intros rows i Hi; unfold Znth.
  replace (nth (Z.to_nat i) (map (@Some Z) rows) None) with
    (nth (Z.to_nat i) (map (@Some Z) rows) (Some 0)).
  - rewrite map_nth; reflexivity.
  - apply nth_indep; rewrite length_map; rewrite Zlength_correct in Hi; lia.
Qed.

(** This entailment consumes the cell AFTER the source store.  It does
    not turn a read of the source array into a write of the destination. *)
Lemma q_query_wait_copy_merge_row : forall output rows initial i,
  Zlength initial = Zlength rows -> 0 <= i < Zlength rows ->
  UCharArray.mixedstoreA output i (Some (Znth i rows 0)) **
    UCharArray.mixed_missing_i output i 0 (Zlength rows)
      (copy_prefix_list (map (@Some Z) rows) initial i) |--
  q_query_wait_copy_rep output rows initial (i + 1).
Proof.
  intros output rows initial i Hlength Hi.
  eapply derivable1_trans.
  - apply UCharArray.mixed_missing_i_merge_to_mixed_full; exact Hi.
  - rewrite <- (q_query_wait_row_initialized rows i Hi).
    rewrite copy_prefix_list_step.
    + reflexivity.
    + rewrite !Zlength_correct, length_map in *; lia.
    + rewrite Zlength_correct, length_map; rewrite Zlength_correct in Hi; exact Hi.
Qed.

Lemma q_query_wait_copy_complete : forall output rows initial i,
  Zlength initial = Zlength rows -> Zlength rows <= i ->
  q_query_wait_copy_rep output rows initial i |-- UCharArray.full output (Zlength rows) rows.
Proof.
  intros output rows initial i Hlength Hdone; unfold q_query_wait_copy_rep.
  rewrite copy_prefix_list_complete.
  - apply UCharArray.mixed_full_to_full.
  - rewrite !Zlength_correct, length_map in *; lia.
  - rewrite Zlength_correct, length_map; rewrite Zlength_correct in Hdone; exact Hdone.
Qed.
