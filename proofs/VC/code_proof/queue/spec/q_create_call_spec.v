Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The C client's ordinary registered history and its carried allocation
    have the SAME endpoints. Only this owned ECB is framed: a Task-only
    history is not silently upgraded to a Some Event-observer trace. The
    spatial source producer must establish the lookup equality while also
    returning the actual bytes, e.g. the strong creator-client producer in
    q_create_proof_helpers. This relation itself owns no heap. *)
Definition q_create_private_interval critical sg invocation eid before after : Prop :=
  critical_region_interval critical sg invocation before after /\
  exists allocation,
    before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    after.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.

Lemma q_create_private_interval_lookup : forall critical sg invocation eid before after allocation,
  q_create_private_interval critical sg invocation eid before after ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  after.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.
Proof. intros critical sg invocation eid before after allocation [_ [current [Hget Hafter]]] Hbefore;
  congruence. Qed.

Lemma q_create_private_interval_refl : forall critical sg invocation eid state allocation,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  q_create_private_interval critical sg invocation eid state state.
Proof. intros; split; [constructor|exists allocation; auto]. Qed.

Lemma q_create_private_interval_trans : forall critical sg invocation eid before middle after,
  q_create_private_interval critical sg invocation eid before middle ->
  q_create_private_interval critical sg invocation eid middle after ->
  q_create_private_interval critical sg invocation eid before after.
Proof.
  intros critical sg invocation eid before middle after
    [Hfirst [first [Hbefore Hmiddle]]] [Hlast [last [Hmiddle' Hafter]]].
  split.
  - eapply KernelResumptionTraceSegment with (stopped1 := false) (stopped2 := false).
    + eapply kernel_resumption_resource_trace_erases; exact Hfirst.
    + eapply kernel_resumption_resource_trace_timer_projection; exact Hfirst.
    + exact Hlast.
  - exists first; split; [exact Hbefore|congruence].
Qed.

Fixpoint q_create_private_stores_interleaved critical sg invocation eid
  (writes : list (EventField * Z)) : program UCOS2_Verify_State unit :=
  match writes with
  | [] => fun before result after => result = tt /\
      q_create_private_interval critical sg invocation eid before after
  | (field, stored) :: rest => fun before result after => exists entry allocation,
      q_create_private_interval critical sg invocation eid before entry /\
      entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      q_create_private_stores_interleaved critical sg invocation eid rest
        (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some stored)) entry)
        result after
  end.

Lemma q_create_private_stores_interleaved_post :
  forall critical sg invocation eid writes before result after allocation,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  q_create_private_stores_interleaved critical sg invocation eid writes before result after ->
  UCOS2_state_inv sg after /\ exists final,
    after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
    final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
    final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
    final.(eventPrivateStorage) = event_create_stores_image allocation.(eventPrivateStorage) writes.
Proof.
  intros critical sg invocation eid writes; induction writes as [|[field stored] rest IH];
    intros before result after allocation Hvalid Hget Hsteps.
  - destruct Hsteps as [_ Htrace].
    pose proof (proj1 (critical_region_interval_transports_resources
      _ _ _ _ _ (proj1 Htrace) Hvalid)) as Hafter.
    pose proof (q_create_private_interval_lookup _ _ _ _ _ _ _ Htrace Hget) as Hlookup.
    split; [exact Hafter|]; exists allocation; repeat split; assumption || reflexivity.
  - destruct Hsteps as [entry [current [Htrace [Hcurrent Htail]]]].
    pose proof (proj1 (critical_region_interval_transports_resources
      _ _ _ _ _ (proj1 Htrace) Hvalid)) as Hentry.
    pose proof (q_create_private_interval_lookup _ _ _ _ _ _ _ Htrace Hget) as Hlookup.
    assert (current = allocation) by congruence; subst current.
    eapply (IH
      (replace_EventS (event_private_write entry.(EventState) eid allocation field (Some stored)) entry)
      result after
      {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
         eventPrivateGeneration := allocation.(eventPrivateGeneration);
         eventPrivateQueue := allocation.(eventPrivateQueue);
         eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
         eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |});
      [|apply kernel_map_set_same|exact Htail].
    eapply UCOS2_event_private_write_preserves_validity; eassumption.
Qed.

Lemma q_create_private_stores_without_interference :
  forall critical sg invocation eid writes before result after allocation,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_create_private_stores eid writes before result after ->
  q_create_private_stores_interleaved critical sg invocation eid writes before result after.
Proof.
  intros critical sg invocation eid writes; induction writes as [|[field stored] rest IH];
    intros before result after allocation Hget Hsteps.
  - destruct Hsteps as [-> ->]; split; [reflexivity|].
    eapply q_create_private_interval_refl; exact Hget.
  - destruct Hsteps as [current [Hcurrent Htail]].
    assert (current = allocation) by congruence; subst current.
    exists before, allocation; split; [eapply q_create_private_interval_refl; exact Hget|].
    split; [exact Hget|]. eapply IH; [apply kernel_map_set_same|exact Htail].
Qed.

(** Source-stage relation for the selected names/IEC-disabled OSQCreate.
    This is a conditional composition interface, NOT an assumed Save
    contract or a theorem about the C function. Its ordinary source history
    and carried-allocation equality require same-endpoint source/heap
    producers. QCB initialization is
    private physical storage; it does not create a second ghost image map.
    [free] is observed at the second Save; [publication_free] is observed
    again at publication. Foreign activity may change either free list. *)
Definition q_create_call_relation (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (start size : Z)
  (slots : list (option addr)) (name : addr)
  (before : UCOS2_Verify_State) (result : addr)
  (after : UCOS2_Verify_State) : Prop :=
  if Z.ltb 0 before.(IntrState).(intNesting) then result = 0 /\ after = before
  else exists entry allocated detached,
    critical_region_interval critical sg invocation before entry /\
    event_create_allocate_critical entry allocated detached /\
    match allocated with
    | None => result = 0 /\ critical_region_interval critical sg invocation detached after
    | Some (eid, image) => exists resumed free reserved_result reserved,
        q_create_private_interval critical sg invocation eid detached resumed /\
        queue_pool_partition sg resumed.(EventState) free /\
        q_create_reserve_critical sg eid free resumed reserved_result reserved /\
        match reserved_result with
        | None => result = 0 /\ critical_region_interval critical sg invocation reserved after
        | Some qid => exists initialized final publication_free,
            q_create_private_stores_interleaved critical sg invocation eid
              (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames)
                2 0 (qcb_addr sg qid) name) reserved tt initialized /\
            initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
            queue_pool_partition sg initialized.(EventState) publication_free /\
            event_name_valid sg initialized.(NameState)
              (q_create_initialized_event final qid start size name) /\
            result = event_pool_addr sg eid /\
            after = replace_EventS
              (queue_publish initialized.(EventState) eid
                (q_create_initialized_event final qid start size name) qid slots) initialized
        end
    end.

Lemma q_create_call_preserves_validity :
  forall critical sg invocation start size slots name before result after,
  UCOS2_state_inv sg before -> 0 < start -> 0 <= size <= 65535 ->
  q_create_call_relation critical sg invocation start size slots name before result after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation start size slots name before result after Hvalid Hstart Hsize Hcall.
  unfold q_create_call_relation in Hcall.
  destruct (Z.ltb 0 before.(IntrState).(intNesting)); [destruct Hcall as [_ ->]; exact Hvalid|].
  destruct Hcall as [entry [allocated [detached [Hentry [Hallocate Hreturn]]]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    _ _ _ _ _ Hentry Hvalid)) as Hentry_valid.
  pose proof (event_create_allocate_critical_preserves_validity sg entry allocated detached
    Hentry_valid Hallocate) as Hdetached.
  destruct allocated as [[eid image]|].
  - destruct Hreturn as [resumed [free [reserved_result [reserved
      [Hresume [Hpartition [Hreserve Hreturn]]]]]]].
    pose proof (proj2 (event_create_allocate_critical_private_result entry eid image detached
      Hallocate)) as Hprivate.
    pose proof (proj1 (critical_region_interval_transports_resources
      _ _ _ _ _ (proj1 Hresume) Hdetached)) as Hresumed.
    pose proof (q_create_private_interval_lookup _ _ _ _ _ _ _ Hresume Hprivate) as Hcurrent.
    assert (Hreserved : UCOS2_state_inv sg reserved).
    { eapply q_create_reserve_critical_preserves_validity;
        [exact Hresumed|exact Hcurrent| |exact Hreserve|reflexivity].
      exact (event_create_allocate_critical_image_type sg entry eid image detached
        Hentry_valid Hallocate). }
    destruct reserved_result as [qid|].
    + destruct Hreturn as [initialized [final [publication_free
        [Hstores [Hfinal [Hpublication [Hname [_ ->]]]]]]]].
      pose proof (q_create_reserve_critical_private_result sg eid free resumed qid reserved
        _ Hcurrent Hreserve) as Howned.
      destruct (q_create_private_stores_interleaved_post
        _ _ _ _ _ _ _ _ _ Hreserved Howned Hstores)
        as [Hinitialized [actual [Hactual [_ [_ [Hqueue _]]]]]].
      assert (actual = final) by congruence; subst actual.
      eapply q_create_publish_preserves_validity;
        [exact Hinitialized|exact Hpublication|exact Hfinal|exact Hqueue|
         exact Hstart|exact Hsize|exact Hname].
    + destruct Hreturn as [_ Hreturn_trace].
      exact (proj1 (critical_region_interval_transports_resources
        _ _ _ _ _ Hreturn_trace Hreserved)).
  - destruct Hreturn as [_ Hreturn_trace].
    exact (proj1 (critical_region_interval_transports_resources
      _ _ _ _ _ Hreturn_trace Hdetached)).
Qed.

(** Unlike the historical noninterleaved rule, this rule does not freeze
    the QCB free list across Restore. The publication-time pool partition
    and binding must come from the CURRENT actual Event/Queue resource
    split. The trace supplies identity/image preservation, never memory.
    All initialized ECB/QCB bytes and the unchanged caller buffer are
    required on the left, and transferred once to the full invariant. *)
Lemma q_create_interleaved_publish_merge :
  forall critical sg task_invocation before initialized free eid allocation final
    qid qcb_image start size slots name,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = Some qid ->
  q_create_private_stores_interleaved critical sg task_invocation eid
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames)
      2 0 (qcb_addr sg qid) name) before tt initialized ->
  initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  queue_published_storage_binding initialized.(EventState) ->
  queue_pool_partition sg initialized.(EventState) free ->
  0 < start -> 0 <= size <= 65535 -> Zlength slots = size ->
  event_name_valid sg initialized.(NameState)
    (q_create_initialized_event final qid start size name) ->
  (event_private_storage_rep sg eid final **
    event_raw_rep sg initialized.(TskState) initialized.(EventState)) **
    (store_map (published_queue_node_rep sg initialized.(EventState))
      initialized.(EventState).(inUsedEventStates) **
      (qcb_storage_rep sg qid (qcb_initialize qcb_image start size) **
        (PtrArray.mixed_full start size slots ** store_free_queue_list sg free))) **
    UCOS2_raw_rep_missing_event_queue sg initialized |--
  UCOS2_inv sg
    (replace_EventS (queue_publish initialized.(EventState) eid
      (q_create_initialized_event final qid start size name) qid slots) initialized).
Proof.
  intros critical sg task_invocation before initialized free eid allocation final
    qid qcb_image start size slots name Hvalid Hget Howner Hstores Hfinal
    Hbinding Hpartition Hstart Hsize Hlength Hname.
  destruct (q_create_private_stores_interleaved_post
    _ _ _ _ _ _ _ _ _ Hvalid Hget Hstores)
    as [Hinitialized [actual [Hactual [_ [_ [Hqueue Himage]]]]]].
  assert (actual = final) by congruence; subst actual.
  rewrite event_create_stores_image_initialization_eq in Himage.
  eapply q_create_publish_merge with (eid_image := allocation.(eventPrivateStorage));
    try eassumption.
  rewrite Hqueue; exact Howner.
Qed.
