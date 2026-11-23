Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSQCreate's native lifecycle, separate from the historical whole-call
    slice in q_create_spec.  Its first ECB pop is exactly
    event_create_allocate_critical.  [free] below is the QCB list observed
    at the SECOND Save, not a list frozen before the intervening Restore.
    The spatial rules tie that observation to the actual root/list cells.
    Private lookup is a source-stage ownership witness, not a C test. *)
Definition q_create_reserve_critical (sg : StableGlobVars) (eid : EventID)
  (free : list QueueID) : program UCOS2_Verify_State (option QueueID) :=
  fun before result after => exists allocation,
    before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    match free with
    | [] => result = None /\
        after = replace_EventS (event_rollback sg before.(EventState) eid allocation) before
    | qid :: _ => result = Some qid /\
        after = replace_EventS (queue_reserve_control_block before.(EventState) eid allocation qid) before
    end.

Lemma q_create_reserve_critical_exists : forall sg before eid allocation free,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  exists result after, q_create_reserve_critical sg eid free before result after.
Proof.
  intros sg before eid allocation [|qid rest] Hget.
  - exists None, (replace_EventS (event_rollback sg before.(EventState) eid allocation) before).
    exists allocation; auto.
  - exists (Some qid), (replace_EventS (queue_reserve_control_block before.(EventState) eid allocation qid) before).
    exists allocation; auto.
Qed.

Lemma q_create_reserve_critical_deterministic : forall sg eid free before r1 s1 r2 s2,
  q_create_reserve_critical sg eid free before r1 s1 ->
  q_create_reserve_critical sg eid free before r2 s2 -> r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid free before r1 s1 r2 s2 [a [Ha Hfirst]] [b [Hb Hsecond]].
  assert (b = a) by congruence; subst b; destruct free;
    destruct Hfirst as [-> ->]; destruct Hsecond as [-> ->]; split; reflexivity.
Qed.

Lemma q_create_reserve_critical_result : forall sg eid free before result after,
  q_create_reserve_critical sg eid free before result after -> result = hd_error free.
Proof. intros sg eid [] before result after [a [_ [-> _]]]; reflexivity. Qed.

Lemma q_create_reserve_critical_task_frame : forall sg eid free before result after,
  q_create_reserve_critical sg eid free before result after -> after.(TskState) = before.(TskState).
Proof. intros sg eid [] before result after [a [_ [_ ->]]]; reflexivity. Qed.

Lemma q_create_reserve_preserves_validity : forall sg before eid allocation qid,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateMutexPCP) = None ->
  UCOS2_state_inv sg
    (replace_EventS (queue_reserve_control_block before.(EventState) eid allocation qid) before).
Proof.
  intros sg before eid allocation qid Hvalid Hget HnoMutexLease.
  eapply UCOS2_event_map_frame_preserves_validity; [exact Hvalid|reflexivity| |].
  - apply functional_extensionality; intro slot.
    unfold event_mutex_lease_view, queue_reserve_control_block, event_set_lifecycle,
      queue_allocation_with_qcb; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec slot eid) as [->|Hne]; [rewrite Hget, HnoMutexLease|]; reflexivity.
  - eapply queue_reserve_control_block_preserves_event_in_range;
      [exact (proj1 (proj2 (proj2 (proj2 Hvalid))))|exact Hget].
Qed.

Lemma q_create_rollback_preserves_validity : forall sg before eid allocation,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some 0 ->
  allocation.(eventPrivateMutexPCP) = None ->
  UCOS2_state_inv sg
    (replace_EventS (event_rollback sg before.(EventState) eid allocation) before).
Proof.
  intros sg before eid allocation Hvalid Hget Htype HnoMutexLease.
  eapply UCOS2_event_map_frame_preserves_validity; [exact Hvalid|reflexivity| |].
  - apply functional_extensionality; intro slot.
    unfold event_mutex_lease_view, event_rollback; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec slot eid) as [->|Hne]; [rewrite Hget, HnoMutexLease|]; reflexivity.
  -
  pose proof Hvalid as [_ [_ [_ [[Hpart [Hfree [Hidentity Hpublished]]] _]]]].
  destruct (event_pool_private_not_free sg before.(EventState) eid allocation Hpart Hget)
    as [_ [_ Hnone]].
  split; [eapply event_rollback_preserves_partition; eassumption|].
  split; [eapply event_rollback_preserves_free_storage; eassumption|].
  split; [eapply event_rollback_preserves_identity; eassumption|exact Hpublished].
Qed.

Lemma q_create_reserve_critical_preserves_validity : forall sg eid free before result after allocation,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some 0 ->
  q_create_reserve_critical sg eid free before result after ->
  allocation.(eventPrivateMutexPCP) = None -> UCOS2_state_inv sg after.
Proof.
  intros sg eid [] before result after allocation Hvalid Hget Htype [a [Ha [_ ->]]] HnoMutexLease;
    assert (a = allocation) by congruence; subst a.
  - eapply q_create_rollback_preserves_validity; eassumption.
  - eapply q_create_reserve_preserves_validity; eassumption.
Qed.

Lemma q_create_reserve_critical_private_result : forall sg eid free before qid after allocation,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  q_create_reserve_critical sg eid free before (Some qid) after ->
  after.(EventState).(eventLifecycle).(eventPrivate) eid =
    Some (queue_allocation_with_qcb allocation qid).
Proof.
  intros sg eid [|head rest] before qid after allocation Hget [a [Ha [Hresult Hafter]]];
    [discriminate|].
  assert (a = allocation) by congruence; subst a.
  injection Hresult as Heq; subst head; subst after; simpl; apply kernel_map_set_same.
Qed.

(** Exhaustion pushes onto the CURRENT ECB free list.  It neither restores
    a pre-Restore snapshot nor rolls back the fresh generation counters. *)
Lemma q_create_reserve_critical_rollback_result : forall sg eid free before after allocation,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  q_create_reserve_critical sg eid free before None after ->
  free = [] /\ after = replace_EventS (event_rollback sg before.(EventState) eid allocation) before.
Proof.
  intros sg eid [|head rest] before after allocation Hget [a [Ha [Hresult Hafter]]];
    [|discriminate].
  assert (a = allocation) by congruence; subst a; auto.
Qed.

(** The source has already updated OSQFreeList on this rule's left side.
    The returned QCB, including its old OSQPtr link, is private storage;
    initialization and publication have not occurred. *)
Lemma q_create_reserve_merge : forall sg before eid allocation qid rest,
  UCOS2_state_inv sg before ->
  queue_published_storage_binding before.(EventState) ->
  queue_pool_partition sg before.(EventState) (qid :: rest) ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  allocation.(eventPrivateMutexPCP) = None ->
  event_raw_rep sg before.(TskState) before.(EventState) **
    (store_map (published_queue_node_rep sg before.(EventState)) before.(EventState).(inUsedEventStates) **
      (sg.(g_OSQFreeList) # Ptr |-> queue_free_head sg rest **
        (free_queue_node sg qid (queue_free_head sg rest) ** store_free_queue_nodes sg rest))) **
    UCOS2_raw_rep_missing_event_queue sg before |--
  free_queue_node sg qid (queue_free_head sg rest) **
    UCOS2_inv sg
      (replace_EventS (queue_reserve_control_block before.(EventState) eid allocation qid) before).
Proof.
  intros sg before eid allocation qid rest Hvalid Hbinding Hpart Hget Hnone HnoMutexLease.
  pose proof (q_create_reserve_preserves_validity sg before eid allocation qid Hvalid Hget HnoMutexLease) as Hpost.
  pose proof (queue_detach_head_reconstructs_storage
    sg before.(EventState) eid allocation qid rest Hbinding Hpart Hget Hnone) as Hpop.
  lazymatch type of Hpop with ?P |-- _ =>
    eapply derivable1_trans with (P ** (event_raw_rep sg before.(TskState) before.(EventState) **
      UCOS2_raw_rep_missing_event_queue sg before))
  end; [entailer!|].
  eapply derivable1_trans; [apply derivable1_sepcon_mono; [exact Hpop|reflexivity]|].
  eapply derivable1_trans with
    (free_queue_node sg qid (queue_free_head sg rest) **
      (event_raw_rep sg before.(TskState)
        (queue_reserve_control_block before.(EventState) eid allocation qid) **
       queue_storage_rep sg (queue_reserve_control_block before.(EventState) eid allocation qid) **
       UCOS2_raw_rep_missing_event_queue sg before)); [entailer!|].
  apply derivable1_sepcon_mono; [reflexivity|].
  apply UCOS2_inv_merge_updated_event_queue; exact Hpost.
Qed.

Lemma q_create_rollback_merge : forall sg before eid allocation,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  allocation.(eventPrivateStorage) EventTypeField = Some 0 ->
  allocation.(eventPrivateMutexPCP) = None ->
  store_map (used_event_rep sg before.(TskState)) before.(EventState).(inUsedEventStates) **
    (event_cell (event_pool_addr sg eid) EventPtrField
       (Some (event_encode_pool_link sg (hd_error before.(EventState).(unUsedEventStates)))) **
     event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
       (event_pool_addr sg eid) allocation.(eventPrivateStorage) EventPtrField **
     event_free_storage_rep sg before.(EventState) **
     sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid) **
    queue_storage_rep sg before.(EventState) ** UCOS2_raw_rep_missing_event_queue sg before |--
  UCOS2_inv sg (replace_EventS (event_rollback sg before.(EventState) eid allocation) before).
Proof.
  intros sg before eid allocation Hvalid Hget Hnone Htype HnoMutexLease.
  pose proof Hvalid as [_ [_ [_ [[Hpart [Hfree _]] _]]]].
  pose proof (q_create_rollback_preserves_validity sg before eid allocation Hvalid Hget Htype HnoMutexLease) as Hpost.
  pose proof (event_rollback_reconstructs_storage
    sg before.(EventState) eid allocation Hpart Hfree Hget) as Hrestore.
  rewrite <- (queue_storage_event_rollback_eq sg before.(EventState) eid allocation Hget Hnone).
  lazymatch type of Hrestore with ?P |-- _ =>
    eapply derivable1_trans with (P **
      (store_map (used_event_rep sg before.(TskState)) before.(EventState).(inUsedEventStates) **
       queue_storage_rep sg (event_rollback sg before.(EventState) eid allocation) **
       UCOS2_raw_rep_missing_event_queue sg before))
  end; [entailer!|].
  sep_apply_l_atomic Hrestore.
  eapply derivable1_trans; [|apply UCOS2_inv_merge_updated_event_queue; exact Hpost].
  unfold event_raw_rep; cbn [event_rollback]; entailer!.
Qed.

(** The action binding carries the actual pre-pop pool observation and
    the first stage's UNUSED/no-QCB facts.  These come from the spatial
    invariant/allocation result; neither is a newly invented runtime test.
    In particular a foreign action cannot select another creator's QCB
    merely by supplying an arbitrary list of supposedly free indices. *)
Definition q_create_reserve_client (task_actor : option nat) (eid : EventID)
  (allocation : EventPrivateAllocation) (free : list QueueID) : KernelClientAction :=
  {| kernel_client_actor := task_actor;
     kernel_client_event_actor := Some allocation.(eventPrivateInvocation);
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
       allocation.(eventPrivateStorage) EventTypeField = Some 0 /\
       allocation.(eventPrivateQueue) = None /\
       queue_pool_partition sg before.(EventState) free /\
       exists result, q_create_reserve_critical sg eid free before result after |}.

Lemma q_create_reserve_client_certificate : forall task_actor eid allocation free,
  allocation.(eventPrivateMutexPCP) = None ->
  KernelClientCertificate (q_create_reserve_client task_actor eid allocation free).
Proof.
  intros task_actor eid allocation free HnoMutexLease; constructor.
  - intros sg before after Hvalid [Hget [Htype [_ [_ [result Hstep]]]]].
    eapply q_create_reserve_critical_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [_ [_ [_ [_ [result Hstep]]]]] Hforeign.
    rewrite (q_create_reserve_critical_task_frame sg eid free before result after Hstep); reflexivity.
  - intros sg before after observer origin Hvalid [_ [_ [_ [_ [result Hstep]]]]] Hnormal Hactive.
    rewrite (q_create_reserve_critical_task_frame sg eid free before result after Hstep); exact Hactive.
  - intros sg before after observer Hvalid [Hget [_ [_ [_ [result [a [Ha Hstep]]]]]]] Hforeign.
    assert (a = allocation) by congruence; subst a.
    change (Some allocation.(eventPrivateInvocation) <> Some observer) in Hforeign.
    destruct free as [|qid rest]; destruct Hstep as [_ ->].
    + eapply event_rollback_frames_other_invocation; [exact Hget|congruence].
    + eapply queue_reserve_frames_other_invocation; [exact Hget|congruence].
Qed.

(** The first allocation's identity/image survives the certified foreign
    interval, so the second critical stage needs no extra assumption that
    its private ECB magically remains allocated.  Actual masking and heap
    frame contracts still have to provide this source interval. *)
Lemma q_create_reserve_after_environment_exists :
  forall critical sg task_invocation before eid image detached resumed free,
  UCOS2_state_inv sg before ->
  event_create_allocate_critical before (Some (eid, image)) detached ->
  critical_region_event_interval critical sg task_invocation
    before.(EventState).(eventLifecycle).(eventNextInvocation) detached resumed ->
  exists result after, q_create_reserve_critical sg eid free resumed result after /\
    UCOS2_state_inv sg after.
Proof.
  intros critical sg task_invocation before eid image detached resumed free Hvalid Hallocate Htrace.
  pose proof (event_create_allocate_critical_preserves_validity sg before
    (Some (eid, image)) detached Hvalid Hallocate) as Hdetached.
  destruct (event_create_allocate_critical_private_result before eid image detached Hallocate)
    as [_ Hget].
  destruct (critical_region_event_interval_transports_resources _ _ _ _ _ _ Htrace Hdetached)
    as [Hresumed [_ [Hframe _]]].
  pose proof (event_creation_frame_lookup _ _ _ _ _ Hframe Hget eq_refl) as Hprivate.
  destruct (q_create_reserve_critical_exists sg resumed eid _ free Hprivate) as [result [after Hstep]].
  exists result, after; split; [exact Hstep|].
  eapply q_create_reserve_critical_preserves_validity;
    [exact Hresumed|exact Hprivate| |exact Hstep|reflexivity].
  exact (event_create_allocate_critical_image_type sg before eid image detached Hvalid Hallocate).
Qed.

(** A failed second allocation returns the first allocation's actual ECB
    to the free list observed after the foreign interval. No old free-list
    snapshot, private lookup, UNUSED type or post-validity is assumed anew. *)
Lemma q_create_failed_reserve_after_environment_merge :
  forall critical sg task_invocation before eid image detached resumed after,
  UCOS2_state_inv sg before ->
  event_create_allocate_critical before (Some (eid, image)) detached ->
  critical_region_event_interval critical sg task_invocation
    before.(EventState).(eventLifecycle).(eventNextInvocation) detached resumed ->
  q_create_reserve_critical sg eid [] resumed None after ->
  store_map (used_event_rep sg resumed.(TskState)) resumed.(EventState).(inUsedEventStates) **
    (event_cell (event_pool_addr sg eid) EventPtrField
       (Some (event_encode_pool_link sg (hd_error resumed.(EventState).(unUsedEventStates)))) **
     event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
       (event_pool_addr sg eid) image EventPtrField **
     event_free_storage_rep sg resumed.(EventState) **
     sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid) **
    queue_storage_rep sg resumed.(EventState) ** UCOS2_raw_rep_missing_event_queue sg resumed |--
  UCOS2_inv sg after.
Proof.
  intros critical sg task_invocation before eid image detached resumed after
    Hvalid Hallocate Hinterval Hreserve.
  pose proof (event_create_allocate_critical_preserves_validity sg before
    (Some (eid, image)) detached Hvalid Hallocate) as Hdetached.
  destruct (event_create_allocate_critical_private_result before eid image detached Hallocate)
    as [_ Hget].
  destruct (critical_region_event_interval_transports_resources _ _ _ _ _ _ Hinterval Hdetached)
    as [Hresumed [_ [Hframe _]]].
  pose proof (event_creation_frame_lookup _ _ _ _ _ Hframe Hget eq_refl) as Hprivate.
  destruct (q_create_reserve_critical_rollback_result sg eid [] resumed after _ Hprivate Hreserve)
    as [_ ->].
  exact (q_create_rollback_merge sg resumed eid
    {| eventPrivateInvocation := before.(EventState).(eventLifecycle).(eventNextInvocation);
       eventPrivateGeneration := before.(EventState).(eventLifecycle).(eventNextGeneration);
       eventPrivateQueue := None; eventPrivateMutexPCP := None; eventPrivateStorage := image |}
    Hresumed Hprivate eq_refl
    (event_create_allocate_critical_image_type sg before eid image detached Hvalid Hallocate) eq_refl).
Qed.

(** The remaining private ECB stores follow the six source-ordered QCB
    stores already represented by qcb_initialize.  The QCB image
    and caller buffer remain local resources until the publication rule;
    there is no second global QCB-image map. *)
Definition q_create_private_event_initialization (sg : StableGlobVars)
  (eid : EventID) (qid : QueueID) (name : addr) :=
  event_create_private_initialization eid sg.(osKernelConfig).(cfgEventNames)
    2 0 (qcb_addr sg qid) name.

Definition q_create_initialized_event (allocation : EventPrivateAllocation)
  (qid : QueueID) (start : addr) (size name : Z) : OSEventAbstractState :=
  {| eventGeneration := allocation.(eventPrivateGeneration);
     eventName := name; eventPadding1 := allocation.(eventPrivateStorage) EventPadding1;
     eventPadding2 := allocation.(eventPrivateStorage) EventPadding2; eventPadding3 := allocation.(eventPrivateStorage) EventPadding3;
     eventPadding19 := allocation.(eventPrivateStorage) EventPadding19;
     eventType := OS_EVENT_TYPE_Q; mutexFields := None;
     semFields := None; mboxFields := None;
     queueFields := Some (queue_initial_fields qid start size); waitList := [] |}.

Lemma q_create_initialized_event_fields_consistency : forall allocation qid start size name,
  event_fields_consistency (q_create_initialized_event allocation qid start size name).
Proof. intros; repeat split; discriminate. Qed.

Lemma q_create_initialized_event_payload_consistency : forall sg allocation qid start size name,
  valid_queue_id sg qid -> 0 < start -> 0 <= size <= 65535 ->
  event_payload_consistency sg (q_create_initialized_event allocation qid start size name).
Proof. intros; apply queue_initial_fields_consistency; assumption. Qed.

Lemma q_create_initialized_event_image : forall sg tasks allocation image qid start size name,
  allocation.(eventPrivateStorage) = event_create_image sg.(osKernelConfig).(cfgEventNames) 2 0 (qcb_addr sg qid) name image ->
  forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field =
      event_image sg tasks (q_create_initialized_event allocation qid start size name) field.
Proof.
  intros sg tasks allocation image qid start size name Himage field Hin;
    destruct sg.(osKernelConfig).(cfgEventNames); destruct field;
    try (exfalso; unfold event_fields in Hin; simpl in Hin; intuition discriminate);
    unfold event_image, q_create_initialized_event;
    rewrite Himage; reflexivity.
Qed.

Lemma q_create_publish_preserves_validity : forall sg before free eid allocation qid start size slots name,
  UCOS2_state_inv sg before ->
  queue_pool_partition sg before.(EventState) free ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = Some qid -> 0 < start -> 0 <= size <= 65535 ->
  event_name_valid sg before.(NameState) (q_create_initialized_event allocation qid start size name) ->
  UCOS2_state_inv sg
    (replace_EventS (queue_publish before.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots) before).
Proof.
  intros sg before free eid allocation qid start size slots name Hvalid Hqpart Hget Howner Hstart Hsize Hname.
  assert (HnoMutexLease : allocation.(eventPrivateMutexPCP) = None).
  { destruct allocation.(eventPrivateMutexPCP) as [pcp|] eqn:Hlease; [|reflexivity].
    pose proof (UCOS2_state_inv_pending_mutex sg before Hvalid) as Hpending.
    assert (Hview : event_mutex_lease_view before.(EventState) eid = Some (pcp, Some qid)).
    { unfold event_mutex_lease_view; rewrite Hget, Hlease, Howner; reflexivity. }
    destruct (Hpending eid pcp (Some qid) Hview) as [_ [_ [Hnone _]]]; discriminate. }
  assert (Hprivate : queue_slot_private before.(EventState) qid).
  { exists eid; unfold queue_private_owner; rewrite Hget; exact Howner. }
  pose proof (proj1 ((proj1 (proj2 Hqpart)) qid) (or_intror Hprivate)) as [Hqid Hnotfree].
  assert (Hfresh : ~ queue_slot_published before.(EventState) qid).
  { intro Hpub; exact ((proj1 (proj2 (proj2 Hqpart))) qid Hpub Hprivate). }
  destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]].
  pose proof Hevents as [Hpool _].
  destruct (event_pool_private_not_free sg before.(EventState) eid allocation Hpool Hget)
    as [_ [_ Hnone]].
  assert (HreferencesAfter : kernel_names_valid sg
    (replace_EventS (queue_publish before.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots) before)).
  { eapply kernel_names_valid_replace_event_add_name with (name := name); [tauto|exact Hname|].
    intros p Hreference.
    exact (event_publish_name_references before.(EventState) eid
      (q_create_initialized_event allocation qid start size name) p Hreference). }
  assert (Hleases : event_mutex_lease_view
    (queue_publish before.(EventState) eid (q_create_initialized_event allocation qid start size name) qid slots) =
    event_mutex_lease_view before.(EventState)).
  { apply event_mutex_lease_view_publish_eq with (allocation := allocation); assumption. }
  assert (HpendingAfter : pending_mutex_consistency sg before.(TskState)
    (queue_publish before.(EventState) eid (q_create_initialized_event allocation qid start size name) qid slots)).
  { eapply pending_mutex_consistency_event_transport with (events := before.(EventState));
      [exact Hleases| |tauto].
    intros slot after Hafter HtypeAfter; cbn [queue_publish event_publish inUsedEventStates] in Hafter.
    unfold kernel_map_set in Hafter; destruct (Z.eq_dec slot eid).
    - injection Hafter as Hafter; subst after; discriminate.
    - exists after; split; [exact Hafter|]. split; [exact HtypeAfter|reflexivity]. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split.
  - change (event_in_range sg before.(TskState)
      (event_publish before.(EventState) eid (q_create_initialized_event allocation qid start size name))).
    eapply event_publish_preserves_in_range;
      [exact Hevents|exact Hget|reflexivity|apply q_create_initialized_event_fields_consistency|
       apply q_create_initialized_event_payload_consistency; assumption| |].
    + intros other old q Hold Hnew Hsame.
      change (Some qid = Some q) in Hnew; injection Hnew as Heq; subst q.
      unfold event_queue_id in Hsame; destruct old.(eventType); try discriminate.
      destruct old.(queueFields) as [fields|] eqn:Hfields; [|discriminate].
      apply Hfresh; exists other, old, fields; repeat split; try assumption; congruence.
    + apply event_wait_entry_consistency_empty; reflexivity.
  - split; [|cbn [replace_EventS]; tauto].
    eapply cross_module_consistency_event_publish with
      (node := q_create_initialized_event allocation qid start size name);
      [exact Hnone|discriminate|reflexivity|reflexivity|exact Hleases|exact Hcross].
Qed.

(** Exact completed private cells and the caller's existing buffer are
    transferred into the shared Event/Queue owners.  The old free OSQPtr
    is not cleared; unused buffer slots may be uninitialized.  Positive
    start and the INT16U domain are resource/arithmetic conditions, not
    runtime checks added to OSQCreate; zero capacity remains represented. *)
Lemma q_create_publish_merge : forall sg before free eid allocation eid_image qid qcb_image start size slots name,
  UCOS2_state_inv sg before ->
  queue_published_storage_binding before.(EventState) ->
  queue_pool_partition sg before.(EventState) free ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = Some qid ->
  allocation.(eventPrivateStorage) = event_create_image sg.(osKernelConfig).(cfgEventNames) 2 0 (qcb_addr sg qid) name eid_image ->
  0 < start -> 0 <= size <= 65535 -> Zlength slots = size ->
  event_name_valid sg before.(NameState) (q_create_initialized_event allocation qid start size name) ->
  (event_private_storage_rep sg eid allocation ** event_raw_rep sg before.(TskState) before.(EventState)) **
    (store_map (published_queue_node_rep sg before.(EventState)) before.(EventState).(inUsedEventStates) **
      (qcb_storage_rep sg qid (qcb_initialize qcb_image start size) **
        (PtrArray.mixed_full start size slots ** store_free_queue_list sg free))) **
    UCOS2_raw_rep_missing_event_queue sg before |--
  UCOS2_inv sg
    (replace_EventS (queue_publish before.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots) before).
Proof.
  intros sg before free eid allocation eid_image qid qcb_image start size slots name
    Hvalid Hbinding Hqpart Hget Howner Himage Hstart Hsize Hlength Hname.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_private_not_free sg before.(EventState) eid allocation Hpool Hget)
    as [_ [_ Hnone]].
  assert (Hprivate : queue_private_owner before.(EventState) eid = Some qid).
  { unfold queue_private_owner; rewrite Hget; exact Howner. }
  pose proof (q_create_publish_preserves_validity sg before free eid allocation qid start size slots name
    Hvalid Hqpart Hget Howner Hstart Hsize Hname) as Hpost.
  pose proof (event_publish_reconstructs_raw_rep_on_fields sg before.(TskState)
    before.(EventState) eid allocation (q_create_initialized_event allocation qid start size name)
    Hpool Hget (q_create_initialized_event_image sg before.(TskState) allocation eid_image qid start size name Himage))
    as Hevent.
  assert (Hqueue :
    store_map (published_queue_node_rep sg before.(EventState)) before.(EventState).(inUsedEventStates) **
      (qcb_storage_rep sg qid (qcb_initialize qcb_image start size) **
       (PtrArray.mixed_full start size slots ** store_free_queue_list sg free)) |--
    queue_storage_rep sg (queue_publish before.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots)).
  { eapply derivable1_trans.
    - apply derivable1_sepcon_mono; [reflexivity|].
      apply derivable1_sepcon_mono;
        [apply qcb_initialize_storage_implies_used|reflexivity].
    - exact (queue_publish_reconstructs_storage sg before.(EventState) free eid
        (q_create_initialized_event allocation qid start size name) (queue_initial_fields qid start size) slots
        Hbinding Hqpart Hprivate Hnone eq_refl eq_refl
        (queue_initial_slots_model qid start size slots Hlength)). }
  lazymatch type of Hevent with ?EP |-- ?EQ =>
    lazymatch type of Hqueue with ?QP |-- ?QQ =>
      eapply derivable1_trans with ((EP ** QP) ** UCOS2_raw_rep_missing_event_queue sg before);
        [entailer!|];
      eapply derivable1_trans with ((EQ ** QQ) ** UCOS2_raw_rep_missing_event_queue sg before)
    end
  end.
  - apply derivable1_sepcon_mono;
      [apply derivable1_sepcon_mono; [exact Hevent|exact Hqueue]|reflexivity].
  - eapply derivable1_trans; [|apply UCOS2_inv_merge_updated_event_queue; exact Hpost]; entailer!.
Qed.

(** Private ECB stores cannot silently change the QCB reservation or any
    published queue's bytes. This transports the pool facts from the second
    allocation cutpoint to publication, instead of assuming them anew. *)
Lemma q_create_private_stores_preserves_queue_pool : forall sg eid writes free before result after,
  queue_pool_partition sg before.(EventState) free ->
  queue_published_storage_binding before.(EventState) ->
  event_create_private_stores eid writes before result after ->
  queue_pool_partition sg after.(EventState) free /\
  queue_published_storage_binding after.(EventState).
Proof.
  intros sg eid writes; induction writes as [|[field value] rest IH];
    intros free before result after Hpart Hbinding Hsteps.
  - destruct Hsteps as [_ ->]; split; assumption.
  - destruct Hsteps as [allocation [Hget Hsteps]].
    set (mid := replace_EventS
      (event_private_write before.(EventState) eid allocation field (Some value)) before).
    assert (HpartMid : queue_pool_partition sg mid.(EventState) free).
    { change (queue_pool_partition sg
        (event_private_write before.(EventState) eid allocation field (Some value)) free).
      unfold queue_pool_partition, queue_slot_private.
      rewrite (queue_private_owner_after_event_private_write
        before.(EventState) eid allocation field (Some value) Hget).
      exact Hpart. }
    assert (HbindingMid : queue_published_storage_binding mid.(EventState)).
    { unfold mid; exact Hbinding. }
    eapply IH; [exact HpartMid|exact HbindingMid|exact Hsteps].
Qed.

(** Source-ordered private initialization connects directly to the existing
    publication rule. Only pre-initialization validity/pool facts are
    supplied; the final allocation's image, reservation and validity are
    derived from the stores. The spatial input still contains the actual
    initialized ECB/QCB and caller buffer, never bytes created by a ghost. *)
Lemma q_create_initialized_publish_merge :
  forall sg before initialized free eid allocation final qid qcb_image start size slots name,
  UCOS2_state_inv sg before ->
  queue_published_storage_binding before.(EventState) ->
  queue_pool_partition sg before.(EventState) free ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = Some qid ->
  q_create_private_event_initialization sg eid qid name before tt initialized ->
  initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  0 < start -> 0 <= size <= 65535 -> Zlength slots = size ->
  event_name_valid sg before.(NameState) (q_create_initialized_event allocation qid start size name) ->
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
  intros sg before initialized free eid allocation final qid qcb_image start size slots name
    Hvalid Hbinding Hpart Hget Howner Hsteps Hfinal Hstart Hsize Hlength Hname.
  destruct (event_create_private_initialization_post eid sg.(osKernelConfig).(cfgEventNames) 2 0 (qcb_addr sg qid) name
    before tt initialized allocation Hget Hsteps)
    as [actual [Hactual [_ [_ [Hqueue Himage]]]]].
  assert (actual = final) by congruence; subst actual.
  destruct (q_create_private_stores_preserves_queue_pool sg eid _ free before tt initialized
    Hpart Hbinding Hsteps) as [HpartAfter HbindingAfter].
  eapply q_create_publish_merge with (eid_image := allocation.(eventPrivateStorage)).
  - eapply event_create_private_stores_preserves_validity; eassumption.
  - exact HbindingAfter.
  - exact HpartAfter.
  - exact Hfinal.
  - rewrite Hqueue; exact Howner.
  - exact Himage.
  - exact Hstart.
  - exact Hsize.
  - exact Hlength.
  - unfold event_name_valid in *; simpl in *.
    rewrite (event_create_private_stores_name_state_eq eid _ before tt initialized Hsteps).
    exact Hname.
Qed.

Definition q_create_publication_client (task_actor : option nat) (eid : EventID)
  (allocation : EventPrivateAllocation) (qid : QueueID) (start : addr) (size : Z)
  (slots : list (option addr)) (name : addr) : KernelClientAction :=
  {| kernel_client_actor := task_actor;
     kernel_client_event_actor := Some allocation.(eventPrivateInvocation);
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
       allocation.(eventPrivateQueue) = Some qid /\
       (exists free, queue_pool_partition sg before.(EventState) free) /\
       event_name_valid sg before.(NameState)
         (q_create_initialized_event allocation qid start size name) /\
       after = replace_EventS (queue_publish before.(EventState) eid
         (q_create_initialized_event allocation qid start size name) qid slots) before |}.

Lemma q_create_publication_client_certificate : forall task_actor eid allocation qid start size slots name,
  0 < start -> 0 <= size <= 65535 ->
  KernelClientCertificate (q_create_publication_client task_actor eid allocation qid start size slots name).
Proof.
  intros task_actor eid allocation qid start size slots name Hstart Hsize; constructor.
  - intros sg before after Hvalid [Hget [Howner [[free Hpart] [Hname ->]]]].
    eapply q_create_publish_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [_ [_ [_ [_ ->]]]] Hforeign; reflexivity.
  - intros sg before after observer origin Hvalid [_ [_ [_ [_ ->]]]] Hnormal Hactive; exact Hactive.
  - intros sg before after observer Hvalid [Hget [_ [_ [_ ->]]]] Hforeign.
    eapply queue_publish_frames_other_invocation; [exact Hget|].
    change (Some allocation.(eventPrivateInvocation) <> Some observer) in Hforeign; congruence.
Qed.
