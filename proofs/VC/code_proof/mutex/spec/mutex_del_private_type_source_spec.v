Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_publication_environment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Import UCOS2_C_Rules EventStateDef EventFieldStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only at an exposed program cut: a private ECB has initialized Type
    different from Mutex. Sem/Mbox/Queue prefixes store tags 3/1/2; the
    repaired MutexCreate performs allocation through Type-last publication
    inside one masked segment. Its intermediate Type=4 private cut is NOT
    claimed to satisfy this property and is not an interruptible boundary.

    This is source provenance, not validity or a public input condition.
    The map and image are the existing Event state; no new ghost field. *)
Definition mutex_del_private_types_non_mutex (events : Glob_EventAbstractState) : Prop :=
  forall eid allocation, events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
    exists kind, allocation.(eventPrivateStorage) EventTypeField = Some kind /\ kind <> 4.

Lemma mutex_del_private_types_defined : forall events,
  mutex_del_private_types_non_mutex events -> event_private_types_defined events.
Proof. intros events Htypes eid allocation Hget; destruct (Htypes eid allocation Hget) as [kind [Hkind _]]; eauto. Qed.

Lemma mutex_del_private_types_initial : forall sg,
  mutex_del_private_types_non_mutex (event_pool_initial sg).
Proof. intros sg eid allocation Hget; discriminate. Qed.

Lemma mutex_del_private_types_allocate : forall sg state result after,
  UCOS2_state_inv sg state -> mutex_del_private_types_non_mutex state.(EventState) ->
  event_create_allocate_critical state result after -> mutex_del_private_types_non_mutex after.(EventState).
Proof.
  intros sg state result after Hvalid Htypes Hstep.
  pose proof Hstep as Hactual; unfold event_create_allocate_critical in Hstep.
  destruct state.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - destruct Hstep as [_ ->]; exact Htypes.
  - destruct Hstep as [image [Himage [-> ->]]].
    intros other allocation Hget.
    cbn [replace_EventS EventState event_detach_head eventLifecycle eventPrivate] in Hget.
    destruct (Z.eq_dec other eid) as [->|Hneq].
    + rewrite kernel_map_set_same in Hget; injection Hget as <-.
      exists 0; split; [eapply event_create_allocate_critical_image_type; eassumption|lia].
    + rewrite kernel_map_set_other in Hget by exact Hneq; eapply Htypes; exact Hget.
Qed.

Lemma mutex_del_private_types_write : forall events eid allocation field value,
  mutex_del_private_types_non_mutex events -> events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (field = EventTypeField -> value <> 4) ->
  mutex_del_private_types_non_mutex (event_private_write events eid allocation field (Some value)).
Proof.
  intros events eid allocation field value Htypes Hget Hsource other updated Hupdated.
  cbn [event_private_write event_set_lifecycle eventLifecycle eventPrivate] in Hupdated.
  destruct (Z.eq_dec other eid) as [->|Hneq].
  - rewrite kernel_map_set_same in Hupdated; injection Hupdated as <-; cbn [eventPrivateStorage].
    destruct (EventField_eq_dec EventTypeField field) as [Hequal|Hdifferent].
    + subst field; exists value; split; [unfold event_write; apply field_update_same|apply Hsource; reflexivity].
    + destruct (Htypes eid allocation Hget) as [kind [Htype Hnot]]; exists kind; split; [|exact Hnot].
      unfold event_write; rewrite field_update_other by congruence; exact Htype.
  - rewrite kernel_map_set_other in Hupdated by exact Hneq; eapply Htypes; exact Hupdated.
Qed.

Lemma mutex_del_private_types_publish : forall events eid node,
  mutex_del_private_types_non_mutex events -> mutex_del_private_types_non_mutex (event_publish events eid node).
Proof.
  intros events eid node Htypes other allocation Hget.
  cbn [event_publish eventLifecycle eventPrivate] in Hget.
  destruct (Z.eq_dec other eid) as [->|Hneq].
  - rewrite kernel_map_set_same in Hget; discriminate.
  - rewrite kernel_map_set_other in Hget by exact Hneq; eapply Htypes; exact Hget.
Qed.

(** This induction follows the actual ordered field list. The full QCB
    and message-array producers of Queue remain distinct obligations. *)
Lemma mutex_del_private_types_prefix : forall eid writes state result after,
  Forall (fun write => fst write = EventTypeField -> snd write <> 4) writes ->
  mutex_del_private_types_non_mutex state.(EventState) ->
  event_create_private_stores eid writes state result after -> mutex_del_private_types_non_mutex after.(EventState).
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; intros state result after Hwrites Htypes Hstep.
  - destruct Hstep as [_ ->]; exact Htypes.
  - inversion Hwrites as [|write tail Hhead Htail]; subst.
    destruct Hstep as [allocation [Hget Hrest]].
    eapply IH; [exact Htail| |exact Hrest]; cbn [replace_EventS EventState].
    eapply mutex_del_private_types_write; eassumption.
Qed.

(** No new requirement is imposed on MutexCreate. Its already checked
    whole critical operation has the SAME pre-existing private map at the
    next exposed cut; allocation/Type-last/publication are not split into
    independent environment actions. *)
Lemma mutex_del_private_types_mutex_publication : forall sg priority state result after,
  UCOS2_state_inv sg state -> mutex_del_private_types_non_mutex state.(EventState) ->
  MutexCreatePublication.critical_operation sg priority state result after ->
  mutex_del_private_types_non_mutex after.(EventState).
Proof.
  intros sg priority state result after Hvalid Htypes Hstep eid allocation Hget.
  rewrite (mutex_del_publication_private_map_eq sg priority state result after Hvalid Hstep) in Hget.
  eapply Htypes; exact Hget.
Qed.

(** Every concrete producer in the existing creator registry preserves
    this exposed-cut fact. A partial initializer field uses its real source
    value; unlike an arbitrary generic store it cannot choose Type=4. *)
Lemma mutex_del_creator_step_preserves_private_non_mutex : forall creator sg cut state next returned,
  UCOS2_state_inv sg state -> mutex_del_private_types_non_mutex state.(EventState) ->
  kernel_client_heap_state_step (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  mutex_del_private_types_non_mutex returned.(EventState).
Proof.
  intros creator sg cut state next returned Hvalid Htypes Hstep.
  assert (Hfields : Forall (fun write => fst write = EventTypeField -> snd write <> 4)
      (mutex_del_creator_fields sg creator)).
  { destruct creator; apply event_create_initialization_fields_non_mutex; lia. }
  destruct Hstep.
  - exact Htypes.
  - exact Htypes.
  - exact Htypes.
  - destruct H.
    + destruct H.
      * destruct H; eapply mutex_del_private_types_allocate; eassumption.
      * unfold mutex_del_creator_published_state; cbn [replace_EventS EventState].
        apply mutex_del_private_types_publish; eapply mutex_del_private_types_prefix; eassumption.
    + exact Htypes.
    + exact Htypes.
    + cbn [replace_EventS EventState].
      eapply mutex_del_private_types_write; [exact Htypes|eassumption|].
      rewrite Forall_forall in Hfields; exact (Hfields (field, stored) H1).
Qed.

(** Actual read from the WHOLE current pool. The type fact selects the
    value; the map split supplies the byte. The same whole pool is retained
    at this masked read cut, to be passed to Restore rather than privately
    framed across it. No default value from the public map is used. *)
Lemma mutex_del_private_pool_type_guard : forall sg state eid allocation heap (frame : Assertion),
  mutex_del_private_types_non_mutex state.(EventState) ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame) heap ->
  exists observed,
    allocation.(eventPrivateStorage) EventTypeField = Some observed /\ observed <> 4 /\
    uchar_load (event_pool_addr sg eid) observed heap /\
    (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame) heap.
Proof.
  intros sg state eid allocation heap frame Htypes Hget Hpre.
  destruct (Htypes eid allocation Hget) as [observed [Htype Hnot]].
  assert (Hopen : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
    event_private_storage_rep sg eid allocation **
      (kernel_program_inv sg state ** event_private_pool_missing_eid sg state.(EventState) eid ** frame)).
  { sep_apply_l_atomic (event_private_pool_split_eid sg state.(EventState) eid allocation Hget); entailer!. }
  exists observed; split; [exact Htype|]. split; [exact Hnot|]. split; [|exact Hpre].
  eapply event_private_storage_type_load; [exact Htype|exact (Hopen heap Hpre)].
Qed.
