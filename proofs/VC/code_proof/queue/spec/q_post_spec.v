Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.

Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSQPost/OSQPostFront/OSQPostOpt, V2.93.01 os_q.c:641--871.
    The discriminant identifies source APIs, not additional kernel state.
    Unknown option bits are accepted; NULL is a valid Queue message.
    The current global wake theorem is for the selected single-Event
    profile, not an assertion of full Multi-enabled API correctness. *)
Inductive QueuePostKind : Type :=
| QueuePostBack
| QueuePostFront
| QueuePostOptions (options : Z).

Definition q_post_broadcast_requested (kind : QueuePostKind) : bool :=
  match kind with
  | QueuePostOptions options => negb (Z.eqb (Z.land options 1) 0)
  | _ => false
  end.

Definition q_post_front_requested (kind : QueuePostKind) : bool :=
  match kind with
  | QueuePostBack => false
  | QueuePostFront => true
  | QueuePostOptions options => negb (Z.eqb (Z.land options 2) 0)
  end.

Definition q_post_wake_requests_schedule (kind : QueuePostKind) : bool :=
  match kind with
  | QueuePostOptions options => Z.eqb (Z.land options 4) 0
  | _ => true
  end.

(** These two observations lie before Save and on opposite sides of the
    ENTER trace call.  [pevent] is the actual C address, NOT the pool index.
    With argument checks disabled a null dereference is not converted to
    an invented error return.  Type checking is unconditional. *)
Definition q_post_argument_error (sg : StableGlobVars) (pevent : addr)
  : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool
  then Some OS_ERR_PEVENT_NULL else None.

Definition q_post_type_error (type_byte : Z) : option OSErrCode :=
  if Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_Q)
  then None else Some OS_ERR_EVENT_TYPE.

Lemma q_post_argument_error_checks_disabled : forall sg pevent,
  sg.(osKernelConfig).(cfgArgumentChecks) = false ->
  q_post_argument_error sg pevent = None.
Proof. intros; unfold q_post_argument_error; rewrite H; reflexivity. Qed.

Lemma q_post_type_error_none_iff : forall type_byte,
  q_post_type_error type_byte = None <-> type_byte = 2.
Proof.
  intros; unfold q_post_type_error; cbn [encode_event_type].
  destruct (Z.eqb type_byte 2) eqn:E; [apply Z.eqb_eq in E|apply Z.eqb_neq in E];
    split; congruence.
Qed.

(** The log records the ignored priority returns for the finite-loop proof;
    it is not a C accumulator.  Every test reads the CURRENT Event bitmap.
    No environment step is inserted inside this masked loop. *)
Definition q_post_broadcast (sg : StableGlobVars) (eid : EventID) (message : addr)
  : UCOS2_Verify_State -> list Priority -> UCOS2_Verify_State -> Prop :=
  event_broadcast sg eid PendQ message PendOK.

Lemma q_post_wake_head : forall sg s eid e head tail message,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> e.(waitList) = head :: tail ->
  exists old,
    s.(TskState).(inUsedTaskStates) head = Some old /\
    event_task_rdy sg s eid PendQ message PendOK =
      Some (old.(curPrio), event_wake_state sg s eid e head old PendQ message PendOK) /\
    UCOS2_state_inv sg
      (event_wake_state sg s eid e head old PendQ message PendOK) /\
    (event_wake_state sg s eid e head old PendQ message PendOK).(EventState).(inUsedEventStates) eid =
      Some (event_set_wait_list e tail).
Proof.
  intros sg s eid e head tail message Hvalid He Htype Hlist.
  apply (event_wake_head sg s eid e head tail PendQ message PendOK);
    [exact Hvalid|exact He|rewrite Htype; reflexivity|exact Hlist].
Qed.

Lemma q_post_broadcast_exists : forall waiters sg s eid e message,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> e.(waitList) = waiters ->
  exists priorities after,
    q_post_broadcast sg eid message s priorities after /\
    UCOS2_state_inv sg after /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e []) /\
    length priorities = length waiters /\
    after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes).
Proof.
  intros waiters sg s eid e message Hvalid He Htype Hlist.
  apply (event_broadcast_exists waiters sg s eid e PendQ message PendOK);
    [exact Hvalid|exact He|rewrite Htype; reflexivity|exact Hlist].
Qed.

Lemma q_post_broadcast_deterministic : forall sg eid message s ps1 s1 ps2 s2,
  q_post_broadcast sg eid message s ps1 s1 ->
  q_post_broadcast sg eid message s ps2 s2 -> ps1 = ps2 /\ s1 = s2.
Proof.
  intros; eapply event_broadcast_deterministic; eassumption.
Qed.

Definition q_post_enqueue (front : bool) (q : QueueFields) (message : addr)
  : option QueueFields :=
  if front then queue_enqueue_front q message else queue_enqueue_back q message.

Definition q_post_enqueue_slots (front : bool) (q : QueueFields) (message : addr)
  (slots : list (option addr)) : list (option addr) :=
  replace_Znth (if front then queue_retreat_index q.(qSize) q.(qOutIndex) else q.(qInIndex))
    (Some message) slots.

(** Critical phase only: AFTER Save, BEFORE Restore.  The boolean is the
    source-local decision to call OS_Sched, not a claim that a switch or a
    return occurs.  Prefix observations must be connected to this entry by
    the handle/trace/platform protocol, not equality across Save/Restore.
    Missing object/storage lookups denote an out-of-domain read, not an
    extra C failure branch.  In particular, the full branch reads no slot. *)
Definition q_post_critical (sg : StableGlobVars) (kind : QueuePostKind)
  (eid : EventID) (message : addr) : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun s result after => exists e,
    s.(EventState).(inUsedEventStates) eid = Some e /\
    if Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0 then
      exists q, e.(queueFields) = Some q /\
      if Z.leb q.(qSize) (queue_entries q) then
        result = (OS_ERR_Q_FULL, false) /\ after = s
      else exists slots next,
        s.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
        q_post_enqueue (q_post_front_requested kind) q message = Some next /\
        result = (OS_ERR_NONE, false) /\
        after = replace_EventS
          (queue_update s.(EventState) eid e next
            (q_post_enqueue_slots (q_post_front_requested kind) q message slots)) s
    else result = (OS_ERR_NONE, q_post_wake_requests_schedule kind) /\
      if q_post_broadcast_requested kind then
        exists priorities, q_post_broadcast sg eid message s priorities after
      else exists priority,
        event_task_rdy sg s eid PendQ message PendOK = Some (priority, after).

Lemma q_post_enqueue_preserves_consistency : forall sg front q message next,
  queue_fields_consistency sg [] q -> q_post_enqueue front q message = Some next ->
  next.(qID) = q.(qID) /\ queue_fields_consistency sg [] next.
Proof.
  intros sg front q message next Hvalid Hstep; split.
  - unfold q_post_enqueue, queue_enqueue_front, queue_enqueue_back in Hstep.
    destruct front; destruct (Z.ltb (queue_entries q) q.(qSize));
      try discriminate; injection Hstep as Hstep; subst next; reflexivity.
  - unfold q_post_enqueue in Hstep; destruct front.
    + eapply queue_enqueue_front_preserves_consistency_total; eauto.
    + eapply queue_enqueue_back_preserves_consistency_total; eauto.
Qed.

Lemma q_post_enqueue_preserves_slots : forall sg front q message slots next,
  queue_fields_consistency sg [] q -> queue_slots_model q slots ->
  q_post_enqueue front q message = Some next ->
  queue_slots_model next (q_post_enqueue_slots front q message slots).
Proof.
  intros sg front q message slots next Hvalid Hslots Hstep.
  unfold q_post_enqueue, q_post_enqueue_slots in *; destruct front.
  - eapply queue_enqueue_front_preserves_slots; eauto.
  - eapply queue_enqueue_back_preserves_slots; eauto.
Qed.

Lemma q_post_broadcast_result : forall sg s eid e message priorities after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  q_post_broadcast sg eid message s priorities after ->
  UCOS2_state_inv sg after /\
  after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e []) /\
  length priorities = length e.(waitList) /\
  after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes).
Proof.
  intros sg s eid e message priorities after Hvalid He Htype Hloop.
  apply (event_broadcast_result sg s eid e PendQ message PendOK priorities after);
    [exact Hvalid|exact He|rewrite Htype; reflexivity|exact Hloop].
Qed.

Lemma q_post_wake_decompose : forall sg s eid e message priority after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  encode_event_wait_grp e.(waitList) s.(TskState) <> 0 ->
  event_task_rdy sg s eid PendQ message PendOK = Some (priority, after) ->
  exists head tail old,
    e.(waitList) = head :: tail /\ s.(TskState).(inUsedTaskStates) head = Some old /\
    priority = old.(curPrio) /\
    after = event_wake_state sg s eid e head old PendQ message PendOK /\
    UCOS2_state_inv sg after /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e tail).
Proof.
  intros sg s eid e message priority after Hvalid He Htype Hnonzero Hstep.
  apply (event_wake_decompose sg s eid e PendQ message PendOK priority after);
    [exact Hvalid|exact He|rewrite Htype; reflexivity|exact Hnonzero|exact Hstep].
Qed.

(** The entire broadcast transports the real residual, including every
    QCB and ring buffer.  The changing TCB/ready/ECB cells must still be
    supplied by their existing per-wake storage reconstruction theorem. *)
Lemma q_post_broadcast_preserves_residual : forall sg eid message s priorities after,
  q_post_broadcast sg eid message s priorities after ->
  forall e, UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros sg eid message s priorities after Hloop e Hvalid He Htype.
  apply (event_broadcast_preserves_residual
    sg eid PendQ message PendOK s priorities after Hloop e Hvalid He).
  rewrite Htype; reflexivity.
Qed.

Lemma q_post_broadcast_task_frame : forall sg eid message s priorities after,
  q_post_broadcast sg eid message s priorities after ->
  forall e tid, UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  ~ In tid e.(waitList) -> after.(TskState).(inUsedTaskStates) tid = s.(TskState).(inUsedTaskStates) tid.
Proof.
  intros sg eid message s priorities after Hloop e tid Hvalid He Htype Habsent.
  apply (event_broadcast_task_frame sg eid PendQ message PendOK s priorities after
    Hloop e tid Hvalid He); [rewrite Htype; reflexivity|exact Habsent].
Qed.

(** Exact recipient observation, not merely an empty final bitmap.
    The transformed TCB carries [Some message] even when message is NULL;
    it retains the source's suspension/status-mask behavior. *)
Lemma q_post_broadcast_delivers_to_waiter : forall sg eid message s priorities after,
  q_post_broadcast sg eid message s priorities after ->
  forall e tid old, UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  In tid e.(waitList) -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old PendQ message PendOK).
Proof.
  intros sg eid message s priorities after Hloop e tid old Hvalid He Htype Hin Hold.
  apply (event_broadcast_updates_waiter sg eid PendQ message PendOK s priorities after
    Hloop e tid old Hvalid He); [rewrite Htype; reflexivity|exact Hin|exact Hold].
Qed.

Lemma q_post_critical_exists : forall sg kind s eid e message,
  UCOS2_state_inv sg s -> queue_published_storage_binding s.(EventState) ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  exists result after, q_post_critical sg kind eid message s result after.
Proof.
  intros sg kind s eid e message Hvalid Hbinding He Htype.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  pose proof Hevents as [_ [_ [_ [_ [Hpayload [_ Hentries]]]]]].
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - pose proof (Hpayload eid e He) as Hqueue.
    unfold event_payload_consistency in Hqueue; rewrite Htype in Hqueue.
    destruct e.(queueFields) as [q|] eqn:Hq; [|contradiction].
    destruct (Z.leb q.(qSize) (queue_entries q)) eqn:Hfull.
    + exists (OS_ERR_Q_FULL, false), s; exists e; split; [exact He|].
      rewrite Hempty; exists q; split; [exact Hq|]; rewrite Hfull; split; reflexivity.
    + destruct (proj1 Hbinding eid e q He Hq) as [_ [slots [Hslots Hmodel]]].
      assert (Hroom : Z.ltb (queue_entries q) q.(qSize) = true)
        by (apply Z.leb_gt in Hfull; apply Z.ltb_lt; exact Hfull).
      assert (Hnext : exists next, q_post_enqueue (q_post_front_requested kind) q message = Some next).
      { unfold q_post_enqueue, queue_enqueue_front, queue_enqueue_back.
        destruct (q_post_front_requested kind); rewrite Hroom; eauto. }
      destruct Hnext as [next Hnext].
      eexists (OS_ERR_NONE, false), _; exists e; split; [exact He|].
      rewrite Hempty; exists q; split; [exact Hq|]; rewrite Hfull.
      exists slots, next; repeat split; eauto.
  - destruct (q_post_broadcast_requested kind) eqn:Hbroadcast.
    + destruct (q_post_broadcast_exists e.(waitList) sg s eid e message Hvalid He Htype eq_refl)
        as [ps [post [Hloop _]]].
      exists (OS_ERR_NONE, q_post_wake_requests_schedule kind), post; exists e;
        split; [exact He|]; rewrite Hempty; split; [reflexivity|].
      rewrite Hbroadcast; exists ps; exact Hloop.
    + destruct e.(waitList) as [|head tail] eqn:Hlist; [discriminate Hempty|].
      destruct (q_post_wake_head sg s eid e head tail message Hvalid He Htype Hlist)
        as [old [_ [Hcall _]]].
      exists (OS_ERR_NONE, q_post_wake_requests_schedule kind),
        (event_wake_state sg s eid e head old PendQ message PendOK).
      exists e; split; [exact He|]; rewrite Hlist, Hempty; split; [reflexivity|].
      rewrite Hbroadcast; exists old.(curPrio); exact Hcall.
Qed.

Lemma q_post_critical_preserves_validity : forall sg kind s eid e message result after,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  q_post_critical sg kind eid message s result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg kind s eid e message result after Hvalid He Htype [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  pose proof Hevents as [_ [_ [_ [_ [Hpayload [_ Hentries]]]]]].
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - apply Z.eqb_eq in Hempty.
    pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg s.(TskState) e.(waitList)
      (proj1 (Hentries eid e He))) Hempty) as Hlist.
    destruct Hstep as [q [Hq Hstep]].
    destruct (Z.leb q.(qSize) (queue_entries q)); [destruct Hstep as [_ ->]; exact Hvalid|].
    destruct Hstep as [slots [next [Hslots [Hnext [_ ->]]]]].
    pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
    rewrite Htype, Hq, Hlist in Hqueue.
    destruct (q_post_enqueue_preserves_consistency sg (q_post_front_requested kind) q message next
      Hqueue Hnext) as [Hid Hnew].
    eapply UCOS2_queue_update_preserves_validity;
      [exact Hvalid|exact He|exact Htype|exact Hq|exact Hid|rewrite Hlist; exact Hnew].
  - apply Z.eqb_neq in Hempty; destruct Hstep as [_ Hstep].
    destruct (q_post_broadcast_requested kind).
    + destruct Hstep as [ps Hloop]; exact (proj1
        (q_post_broadcast_result sg s eid e message ps after Hvalid He Htype Hloop)).
    + destruct Hstep as [p Hcall].
      destruct (q_post_wake_decompose sg s eid e message p after Hvalid He Htype Hempty Hcall)
        as [head [tail [old [_ [_ [_ [_ [Hpost _]]]]]]]]; exact Hpost.
Qed.

Lemma q_post_critical_error_frame : forall sg kind s eid message result after,
  q_post_critical sg kind eid message s result after -> fst result <> OS_ERR_NONE ->
  result = (OS_ERR_Q_FULL, false) /\ after = s.
Proof.
  intros sg kind s eid message result after [e [He Hstep]] Herror.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0).
  - destruct Hstep as [q [Hq Hstep]]; destruct (Z.leb q.(qSize) (queue_entries q)); [exact Hstep|].
    destruct Hstep as [slots [next [_ [_ [Hr _]]]]]; subst result; contradiction Herror; reflexivity.
  - destruct Hstep as [Hr _]; subst result; contradiction Herror; reflexivity.
Qed.

Lemma q_post_critical_requests_schedule_iff : forall sg kind s eid e message result after,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  q_post_critical sg kind eid message s result after ->
  (snd result = true <->
    encode_event_wait_grp e.(waitList) s.(TskState) <> 0 /\
    q_post_wake_requests_schedule kind = true).
Proof.
  intros sg kind s eid e message result after He [node [Hnode Hstep]].
  assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - apply Z.eqb_eq in Hempty; destruct Hstep as [q [Hq Hstep]].
    destruct (Z.leb q.(qSize) (queue_entries q)).
    + destruct Hstep as [-> _]; simpl; split; [discriminate|tauto].
    + destruct Hstep as [slots [next [_ [_ [-> _]]]]]; simpl; split; [discriminate|tauto].
  - apply Z.eqb_neq in Hempty; destruct Hstep as [-> _]; simpl; tauto.
Qed.

(** Retain the distinct write orders of Post and PostOpt.  The shared
    Queue image theorems connect these literal QCB writes to the endpoint;
    the buffer slot write is represented separately by enqueue_slots. *)
Definition q_post_qcb_writes (kind : QueuePostKind) (q : QueueFields)
  (image : QCBStorage) : QCBStorage :=
  match kind with
  | QueuePostBack => qcb_enqueue_back q image
  | QueuePostFront => qcb_enqueue_front q image
  | QueuePostOptions options =>
      if q_post_front_requested (QueuePostOptions options)
      then qcb_enqueue_front q image else qcb_enqueue_back_wrap_first q image
  end.

Lemma q_post_qcb_writes_fields_eq : forall kind q message next,
  q_post_enqueue (q_post_front_requested kind) q message = Some next ->
  q_post_qcb_writes kind q (qcb_fields_image q) = qcb_fields_image next.
Proof.
  intros kind q message next Hstep; destruct kind; cbn [q_post_qcb_writes].
  - eapply qcb_enqueue_back_fields_eq; exact Hstep.
  - eapply qcb_enqueue_front_fields_eq; exact Hstep.
  - unfold q_post_enqueue in Hstep; destruct (q_post_front_requested (QueuePostOptions options)).
    + eapply qcb_enqueue_front_fields_eq; exact Hstep.
    + eapply qcb_enqueue_back_wrap_first_fields_eq; exact Hstep.
Qed.

Lemma q_post_enqueue_merge_global : forall sg kind s eid e q message next slots free,
  UCOS2_state_inv sg s ->
  queue_published_storage_binding s.(EventState) ->
  queue_pool_partition sg s.(EventState) free ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  e.(queueFields) = Some q -> e.(waitList) = [] -> queue_slots_model q slots ->
  q_post_enqueue (q_post_front_requested kind) q message = Some next ->
  let written := q_post_enqueue_slots (q_post_front_requested kind) q message slots in
  (event_raw_rep sg s.(TskState) s.(EventState) **
    (store_map_missing_i (published_queue_node_rep sg s.(EventState))
       s.(EventState).(inUsedEventStates) eid **
      ((used_queue_control_block sg next ** PtrArray.mixed_full next.(qStart) next.(qSize) written) **
        store_free_queue_list sg free))) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (replace_EventS (queue_update s.(EventState) eid e next written) s).
Proof.
  intros sg kind s eid e q message next slots free Hvalid Hbinding Hpartition He Htype Hq Hlist
    Hslots Hnext written.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
  rewrite Htype, Hq, Hlist in Hqueue.
  destruct (q_post_enqueue_preserves_consistency sg (q_post_front_requested kind) q message next
    Hqueue Hnext) as [Hid Hnew].
  eapply UCOS2_inv_merge_queue_update;
    [exact Hvalid|exact Hbinding|exact Hpartition|exact He|exact Htype|exact Hq|exact Hid| |].
  - rewrite Hlist; exact Hnew.
  - eapply q_post_enqueue_preserves_slots; eauto.
Qed.
