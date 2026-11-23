Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
From AUXLib Require Import Axioms Feq ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** V2.93.01 SemCreate/MboxCreate: IEC check, ISR check, Save/free-pop/
    Restore, then private Type/Cnt/Ptr/[Name]/WaitListInit stores and trace.
    There is no scheduler-lock check or perr output.  An IEC hook that
    returns is followed by NULL; its actual call contract is separate. *)
Definition event_create_runtime_exception_requested (sg : StableGlobVars) (started : Z) : bool :=
  (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && Z.eqb started 1)%bool.

Definition event_create_isr_rejected (nesting : Z) : bool := Z.ltb 0 nesting.

(** The result carries the actual detached image as a proof observation,
    not as an extra C return. Task calling context remains in the surrounding
    invocation/critical-region protocol, not in the private ECB image. *)
Definition event_create_allocate_critical
  : program UCOS2_Verify_State (option (EventID * EventStorage)) :=
  fun s result after =>
    match s.(EventState).(unUsedEventStates) with
    | [] => result = None /\ after = s
    | eid :: rest => exists image,
        s.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
        result = Some (eid, image) /\
        after = replace_EventS (event_detach_head s.(EventState) eid rest image) s
    end.

Definition event_create_return_ptr (sg : StableGlobVars)
  (result : option (EventID * EventStorage)) : addr :=
  match result with None => 0 | Some (eid, _) => event_pool_addr sg eid end.

Lemma event_create_allocate_critical_exists : forall sg s,
  UCOS2_state_inv sg s ->
  exists result after, event_create_allocate_critical s result after.
Proof.
  intros sg s Hvalid; unfold event_create_allocate_critical.
  destruct s.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hfree.
  - exists None, s; split; reflexivity.
  - pose proof Hvalid as [_ [_ [_ [[_ [[Hdomain _] _]] _]]]].
    destruct (proj2 (Hdomain eid) ltac:(rewrite Hfree; simpl; auto)) as [image Himage].
    exists (Some (eid, image)), (replace_EventS (event_detach_head s.(EventState) eid rest image) s).
    exists image; repeat split; assumption || reflexivity.
Qed.

Lemma event_create_allocate_critical_deterministic : forall s r1 s1 r2 s2,
  event_create_allocate_critical s r1 s1 -> event_create_allocate_critical s r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros s r1 s1 r2 s2; unfold event_create_allocate_critical.
  destruct s.(EventState).(unUsedEventStates) as [|eid rest].
  - intros [-> ->] [-> ->]; split; reflexivity.
  - intros [image [Himage [-> ->]]] [other [Hother [-> ->]]].
    assert (other = image) by congruence; subst other; split; reflexivity.
Qed.

Lemma event_create_allocate_critical_preserves_validity : forall sg s result after,
  UCOS2_state_inv sg s -> event_create_allocate_critical s result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg s result after Hvalid; unfold event_create_allocate_critical.
  destruct s.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hfree.
  - intros [_ ->]; exact Hvalid.
  - intros [image [_ [_ ->]]]; eapply UCOS2_event_detach_head_preserves_validity; eassumption.
Qed.

Lemma event_create_allocate_critical_empty_frame : forall s after,
  event_create_allocate_critical s None after ->
  s.(EventState).(unUsedEventStates) = [] /\ after = s.
Proof.
  intros s after; unfold event_create_allocate_critical.
  destruct s.(EventState).(unUsedEventStates); [tauto|intros [image [_ [H _]]]; discriminate].
Qed.

Lemma event_create_allocate_critical_task_frame : forall s result after,
  event_create_allocate_critical s result after -> after.(TskState) = s.(TskState).
Proof.
  intros s result after; unfold event_create_allocate_critical.
  destruct s.(EventState).(unUsedEventStates).
  - intros [_ ->]; reflexivity.
  - intros [image [_ [_ ->]]]; reflexivity.
Qed.

Lemma event_create_allocate_critical_image_type : forall sg s eid image after,
  UCOS2_state_inv sg s ->
  event_create_allocate_critical s (Some (eid, image)) after ->
  image EventTypeField = Some 0.
Proof.
  intros sg s eid image after Hvalid; unfold event_create_allocate_critical.
  destruct s.(EventState).(unUsedEventStates) as [|head rest];
    [intros [Hnone _]; discriminate|].
  intros [bytes [Hbytes [Heq _]]]; injection Heq as Heid Himage; subst head bytes.
  pose proof Hvalid as [_ [_ [_ [[_ [[_ [_ Htypes]] _]] _]]]].
  eapply Htypes; exact Hbytes.
Qed.

Lemma event_create_allocate_critical_private_result : forall s eid image after,
  event_create_allocate_critical s (Some (eid, image)) after ->
  after.(EventState).(inUsedEventStates) = s.(EventState).(inUsedEventStates) /\
  after.(EventState).(eventLifecycle).(eventPrivate) eid = Some
    {| eventPrivateInvocation := s.(EventState).(eventLifecycle).(eventNextInvocation);
       eventPrivateGeneration := s.(EventState).(eventLifecycle).(eventNextGeneration);
       eventPrivateQueue := None; eventPrivateMutexPCP := None;
       eventPrivateStorage := image |}.
Proof.
  intros s eid image after; unfold event_create_allocate_critical.
  destruct s.(EventState).(unUsedEventStates) as [|head rest]; [intros [H _]; discriminate|].
  intros [bytes [_ [Heq ->]]]; injection Heq as Heid Himage; subst head bytes.
  split; [reflexivity|apply kernel_map_set_same].
Qed.

(** One source field store at a time.  A missing private allocation makes
    this relation inapplicable; it is NOT a check inserted into the C code.
    This relation alone owns no memory and models no intervening ISR or
    trace call.  Each real store uses the spatial rule below, and external
    steps must preserve the invocation-owned allocation and storage. *)
Fixpoint event_create_private_stores (eid : EventID) (writes : list (EventField * Z))
  : program UCOS2_Verify_State unit :=
  match writes with
  | [] => fun s result after => result = tt /\ after = s
  | (field, stored) :: rest => fun s result after => exists allocation,
      s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      event_create_private_stores eid rest
        (replace_EventS (event_private_write s.(EventState) eid allocation field (Some stored)) s)
        result after
  end.

Definition event_create_stores_image (image : EventStorage) (writes : list (EventField * Z))
  : EventStorage :=
  fold_left (fun before write => event_write before (fst write) (Some (snd write))) writes image.

Definition event_create_initialization_fields (named : bool) (kind count pointer name : Z)
  : list (EventField * Z) :=
  [(EventTypeField, kind); (EventCntField, count); (EventPtrField, pointer)] ++
  (if named then [(EventNameField, name)] else []) ++
  [(EventGrpField, 0)] ++ map (fun row => (event_table_field (Z.of_nat row), 0)) (seq 0 8).

Definition event_create_private_initialization (eid : EventID) (named : bool) (kind count pointer name : Z)
  : program UCOS2_Verify_State unit :=
  event_create_private_stores eid (event_create_initialization_fields named kind count pointer name).

Lemma event_create_stores_image_initialization_eq : forall image named kind count pointer name,
  event_create_stores_image image (event_create_initialization_fields named kind count pointer name) =
  event_create_image named kind count pointer name image.
Proof. intros image []; reflexivity. Qed.

Lemma event_create_private_stores_exists : forall eid writes s allocation,
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  exists after, event_create_private_stores eid writes s tt after.
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; intros s allocation Hget.
  - exists s; split; reflexivity.
  - cbn [event_create_private_stores].
    destruct (IH (replace_EventS (event_private_write s.(EventState) eid allocation field (Some value)) s)
      _ (kernel_map_set_same _ _ _ _)) as [after Hafter].
    exists after, allocation; split; assumption.
Qed.

Lemma event_create_private_stores_deterministic : forall eid writes s r1 s1 r2 s2,
  event_create_private_stores eid writes s r1 s1 -> event_create_private_stores eid writes s r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; cbn [event_create_private_stores].
  - intros s r1 s1 r2 s2 [-> ->] [-> ->]; split; reflexivity.
  - intros s r1 s1 r2 s2 [a [Ha Hfirst]] [b [Hb Hsecond]].
    assert (b = a) by congruence; subst b; eapply IH; eassumption.
Qed.

Lemma event_create_private_stores_preserves_validity : forall sg eid writes s result after,
  UCOS2_state_inv sg s -> event_create_private_stores eid writes s result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg eid writes; induction writes as [|[field value] rest IH]; intros s result after Hvalid;
    cbn [event_create_private_stores].
  - intros [_ ->]; exact Hvalid.
  - intros [allocation [Hget Hsteps]]; eapply IH; [|exact Hsteps].
    eapply UCOS2_event_private_write_preserves_validity; eassumption.
Qed.

Lemma event_create_private_stores_post_allocation : forall eid writes s result after allocation,
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_create_private_stores eid writes s result after ->
  exists final,
    after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
    final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
    final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
    final.(eventPrivateStorage) = event_create_stores_image allocation.(eventPrivateStorage) writes.
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; intros s result after allocation Hget;
    cbn [event_create_private_stores].
  - intros [_ ->]; exists allocation; repeat split; assumption || reflexivity.
  - intros [current [Hcurrent Hsteps]]; assert (current = allocation) by congruence; subst current.
    destruct (IH
      (replace_EventS (event_private_write s.(EventState) eid allocation field (Some value)) s)
      result after _ (kernel_map_set_same _ _ _ _) Hsteps) as [final Hfinal].
    exists final; exact Hfinal.
Qed.

Lemma event_create_private_stores_published_frame : forall eid writes s result after,
  event_create_private_stores eid writes s result after ->
  after.(EventState).(inUsedEventStates) = s.(EventState).(inUsedEventStates) /\
  after.(EventState).(publishedQueueBytes) = s.(EventState).(publishedQueueBytes) /\
  after.(TskState) = s.(TskState) /\ after.(SchedState) = s.(SchedState).
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; intros s result after;
    cbn [event_create_private_stores].
  - intros [_ ->]; repeat split; reflexivity.
  - intros [allocation [_ Hsteps]]; exact (IH _ _ _ Hsteps).
Qed.

Lemma event_create_private_stores_mutex_pcp_eq : forall eid writes before result after allocation final,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_create_private_stores eid writes before result after ->
  after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  final.(eventPrivateMutexPCP) = allocation.(eventPrivateMutexPCP).
Proof.
  intros eid writes; induction writes as [|[field stored] rest IH];
    intros before result after allocation final Hget Hsteps Hfinal.
  - destruct Hsteps as [_ ->]; assert (final = allocation) by congruence; subst; reflexivity.
  - destruct Hsteps as [current [Hcurrent Htail]].
    assert (current = allocation) by congruence; subst current.
    exact (IH (replace_EventS
      (event_private_write before.(EventState) eid allocation field (Some stored)) before) result after
      {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
         eventPrivateGeneration := allocation.(eventPrivateGeneration);
         eventPrivateQueue := allocation.(eventPrivateQueue);
         eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
         eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |}
      final (kernel_map_set_same _ _ _ _) Htail Hfinal).
Qed.

Lemma event_create_private_stores_name_state_eq : forall eid writes s result after,
  event_create_private_stores eid writes s result after ->
  after.(NameState) = s.(NameState).
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; intros s result after;
    cbn [event_create_private_stores].
  - intros [_ ->]; reflexivity.
  - intros [allocation [_ Hsteps]]; exact (IH _ _ _ Hsteps).
Qed.

Lemma event_create_private_initialization_post : forall eid named kind count pointer name s result after allocation,
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_create_private_initialization eid named kind count pointer name s result after ->
  exists final,
    after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
    final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
    final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
    final.(eventPrivateStorage) = event_create_image named kind count pointer name allocation.(eventPrivateStorage).
Proof.
  intros eid named kind count pointer name s result after allocation Hget Hsteps.
  destruct (event_create_private_stores_post_allocation eid _ s result after allocation Hget Hsteps)
    as [final Hfinal]; rewrite event_create_stores_image_initialization_eq in Hfinal.
  exists final; exact Hfinal.
Qed.

Lemma event_create_private_stores_unpublished : forall sg eid writes s result after allocation,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_create_private_stores eid writes s result after ->
  after.(EventState).(inUsedEventStates) eid = None /\ ~ In eid after.(EventState).(unUsedEventStates).
Proof.
  intros sg eid writes s result after allocation Hvalid Hget Hsteps.
  destruct (event_create_private_stores_post_allocation eid writes s result after allocation Hget Hsteps)
    as [final [Hfinal _]].
  pose proof (event_create_private_stores_preserves_validity sg eid writes s result after Hvalid Hsteps)
    as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_private_not_free sg after.(EventState) eid final Hpool Hfinal)
    as [_ [Hfree Hused]]; split; assumption.
Qed.

Lemma event_create_private_store_merge : forall sg s eid allocation field value,
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  (event_cell (event_pool_addr sg eid) field (Some value) **
   event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) allocation.(eventPrivateStorage) field) **
    UCOS2_inv sg s |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_write allocation.(eventPrivateStorage) field (Some value)) **
  UCOS2_inv sg
    (replace_EventS (event_private_write s.(EventState) eid allocation field (Some value)) s).
Proof.
  intros sg s eid allocation field value Hget Hfield.
  apply derivable1_sepcon_mono.
  - apply event_storage_merge_updated_field; exact Hfield.
  - apply UCOS2_event_private_write_global_frame; exact Hget.
Qed.

(** Environment-action bindings for the already defined source stages.
    The Task actor is the enclosing execution invocation, while the Event
    actor is the allocator's independent invocation.  The equality in the
    allocation binding names the actual next identifier; it is not a C
    runtime guard.  Physical source embedding/Save/Restore/trace contracts
    still consume the separate spatial rules and the caller's resources. *)
Definition event_create_allocate_client (task_actor : option nat)
  (invocation : nat) : KernelClientAction :=
  {| kernel_client_actor := task_actor; kernel_client_event_actor := Some invocation;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       invocation = before.(EventState).(eventLifecycle).(eventNextInvocation) /\
       exists result, event_create_allocate_critical before result after |}.

Lemma event_create_allocate_client_certificate : forall task_actor invocation,
  KernelClientCertificate (event_create_allocate_client task_actor invocation).
Proof.
  intros task_actor invocation; constructor.
  - intros sg before after Hvalid [_ [result Hstep]].
    eapply event_create_allocate_critical_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [_ [result Hstep]] Hforeign.
    rewrite (event_create_allocate_critical_task_frame before result after Hstep); reflexivity.
  - intros sg before after observer call_origin Hvalid [_ [result Hstep]] Hnormal Hactive.
    rewrite (event_create_allocate_critical_task_frame before result after Hstep); exact Hactive.
  - intros sg before after observer Hvalid [Hinv [result Hstep]] Hforeign.
    change (Some invocation <> Some observer) in Hforeign.
    unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]].
      pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
      destruct (event_pool_free_unallocated sg before.(EventState) eid Hpool
        ltac:(rewrite Hhead; simpl; auto)) as [_ Hnone].
      eapply event_detach_frames_other_invocation; [exact Hnone|congruence].
Qed.

Definition event_create_private_store_client (task_actor : option nat) (eid : EventID)
  (allocation : EventPrivateAllocation) (field : EventField) (stored : Z) : KernelClientAction :=
  {| kernel_client_actor := task_actor;
     kernel_client_event_actor := Some allocation.(eventPrivateInvocation);
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
       after = replace_EventS (event_private_write before.(EventState) eid allocation field (Some stored)) before |}.

Lemma event_create_private_store_client_certificate : forall task_actor eid allocation field stored,
  KernelClientCertificate (event_create_private_store_client task_actor eid allocation field stored).
Proof.
  intros task_actor eid allocation field stored; constructor.
  - intros sg before after Hvalid [Hget ->].
    eapply UCOS2_event_private_write_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [Hget ->] Hforeign; reflexivity.
  - intros sg before after observer origin Hvalid [Hget ->] Hnormal Hactive; exact Hactive.
  - intros sg before after observer Hvalid [Hget ->] Hforeign.
    eapply event_private_write_frames_other_invocation; [exact Hget|].
    change (Some allocation.(eventPrivateInvocation) <> Some observer) in Hforeign; congruence.
Qed.

(** Logical publication is the resource transfer at the completed-handle
    boundary, not another C assignment.  Well-formedness is proved by a
    payload factory in the certificate, not tested by the source relation.
    Matching initialized bytes and QCB ownership remain spatial obligations.
    The name condition is the caller's resource protocol, like the existing
    Task publication protocol, not a new C test.  The raw [event_publish]
    transformer is unchanged; an enabled name must come from the real Name
    owner before the pointer can become a shared root. *)
Definition event_create_publication_client (task_actor : option nat) (eid : EventID)
  (allocation : EventPrivateAllocation) (node : OSEventAbstractState) : KernelClientAction :=
  {| kernel_client_actor := task_actor;
     kernel_client_event_actor := Some allocation.(eventPrivateInvocation);
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
       event_name_valid sg before.(NameState) node /\
       after = replace_EventS (event_publish before.(EventState) eid node) before |}.

Lemma event_create_publication_client_certificate : forall task_actor eid allocation node,
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = [] ->
  event_fields_consistency node -> (forall sg, event_payload_consistency sg node) ->
  allocation.(eventPrivateMutexPCP) = None ->
  KernelClientCertificate (event_create_publication_client task_actor eid allocation node).
Proof.
  intros task_actor eid allocation node Hgeneration Hnonmutex Hqueue Hempty Hfields Hpayload HnoMutexLease; constructor.
  - intros sg before after Hvalid [Hget [Hname ->]].
    eapply UCOS2_event_publish_preserves_validity; try eassumption; apply Hpayload.
  - intros sg before after observer Hvalid [Hget [Hname ->]] Hforeign; reflexivity.
  - intros sg before after observer origin Hvalid [Hget [Hname ->]] Hnormal Hactive; exact Hactive.
  - intros sg before after observer Hvalid [Hget [Hname ->]] Hforeign.
    eapply event_publish_frames_other_invocation; [exact Hget|].
    change (Some allocation.(eventPrivateInvocation) <> Some observer) in Hforeign; congruence.
Qed.

Lemma event_create_environment_preserves_allocation :
  forall critical sg task_invocation event_invocation before after eid allocation,
  critical_region_event_interval critical sg task_invocation event_invocation before after ->
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  after.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
  after.(EventState).(inUsedEventStates) eid = None /\ ~ In eid after.(EventState).(unUsedEventStates).
Proof.
  intros critical sg task_invocation event_invocation before after eid allocation Htrace Hvalid Hget Hinv.
  destruct (critical_region_event_interval_transports_resources _ _ _ _ _ _ Htrace Hvalid)
    as [Hpost [_ [Hframe _]]].
  pose proof (event_creation_frame_lookup event_invocation before.(EventState) after.(EventState)
    eid allocation Hframe Hget Hinv) as Hafter.
  pose proof Hpost as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_private_not_free sg after.(EventState) eid allocation Hpool Hafter)
    as [_ [Hfree Hused]].
  split; [exact Hafter|]; split; assumption.
Qed.
