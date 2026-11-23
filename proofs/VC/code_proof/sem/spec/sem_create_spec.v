Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.VC.code.event.spec.event_create_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Configured SemCreate stores; [name] is the actual source literal's
    address when names are enabled, not a newly allocated string.  The common allocate stage
    occurs before Restore; this initialization occurs afterwards.  The
    count bound in the validity theorem is the INT16U argument domain,
    not a guard added to the implementation. *)
Definition sem_create_private_initialization (sg : StableGlobVars)
  (eid : EventID) (count name : Z) :=
  event_create_private_initialization eid sg.(osKernelConfig).(cfgEventNames) 3 count 0 name.

Definition sem_create_event (allocation : EventPrivateAllocation) (count name : Z) : OSEventAbstractState :=
  {| eventGeneration := allocation.(eventPrivateGeneration);
     eventName := name; eventPadding1 := allocation.(eventPrivateStorage) EventPadding1;
     eventPadding2 := allocation.(eventPrivateStorage) EventPadding2; eventPadding3 := allocation.(eventPrivateStorage) EventPadding3;
     eventPadding19 := allocation.(eventPrivateStorage) EventPadding19;
     eventType := OS_EVENT_TYPE_SEM; mutexFields := None;
     semFields := Some {| semCount := count |}; mboxFields := None;
     queueFields := None; waitList := [] |}.

Lemma sem_create_event_fields_consistency : forall allocation count name,
  event_fields_consistency (sem_create_event allocation count name).
Proof. intros; repeat split; discriminate. Qed.

Lemma sem_create_event_payload_consistency : forall sg allocation count name,
  0 <= count <= 65535 -> event_payload_consistency sg (sem_create_event allocation count name).
Proof. intros sg allocation count name Hcount; split; [exact Hcount|intros H; contradiction]. Qed.

Lemma sem_create_image_matches_event : forall sg tasks allocation image count name,
  allocation.(eventPrivateStorage) = event_create_image sg.(osKernelConfig).(cfgEventNames) 3 count 0 name image ->
  forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg tasks (sem_create_event allocation count name) field.
Proof.
  intros sg tasks allocation image count name Himage field Hin;
    destruct sg.(osKernelConfig).(cfgEventNames); destruct field;
    try (exfalso; unfold event_fields in Hin; simpl in Hin; intuition discriminate);
    unfold event_image, sem_create_event; rewrite Himage; reflexivity.
Qed.

Lemma sem_create_publish_preserves_validity : forall sg s eid allocation count name,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  0 <= count <= 65535 ->
  event_name_valid sg s.(NameState) (sem_create_event allocation count name) ->
  allocation.(eventPrivateMutexPCP) = None ->
  UCOS2_state_inv sg
    (replace_EventS (event_publish s.(EventState) eid (sem_create_event allocation count name)) s).
Proof.
  intros sg s eid allocation count name Hvalid Hget Hcount Hname HnoMutexLease.
  eapply UCOS2_event_publish_preserves_validity;
    [exact Hvalid|exact Hget|reflexivity|discriminate|reflexivity|reflexivity| | |exact Hname|exact HnoMutexLease].
  - apply sem_create_event_fields_consistency.
  - apply sem_create_event_payload_consistency; exact Hcount.
Qed.

(** Publication consumes the completed real ECB.  The common rule keeps
    every other Event, all QCBs/buffers and the remaining global heap. *)
Lemma sem_create_publish_merge : forall sg s eid allocation image count name,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  allocation.(eventPrivateStorage) = event_create_image sg.(osKernelConfig).(cfgEventNames) 3 count 0 name image ->
  0 <= count <= 65535 ->
  event_name_valid sg s.(NameState) (sem_create_event allocation count name) ->
  allocation.(eventPrivateMutexPCP) = None ->
  event_private_storage_rep sg eid allocation **
    (event_raw_rep sg s.(TskState) s.(EventState) **
     queue_storage_rep sg s.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg s) |--
  UCOS2_inv sg
    (replace_EventS (event_publish s.(EventState) eid (sem_create_event allocation count name)) s).
Proof.
  intros sg s eid allocation image count name Hvalid Hget Hqueue Himage Hcount Hname HnoMutexLease.
  eapply UCOS2_inv_merge_event_publish;
    [exact Hvalid|exact Hget|exact Hqueue| |reflexivity|discriminate|reflexivity|reflexivity| | |exact Hname|exact HnoMutexLease].
  - eapply sem_create_image_matches_event; exact Himage.
  - apply sem_create_event_fields_consistency.
  - apply sem_create_event_payload_consistency; exact Hcount.
Qed.

Definition sem_create_publication_client (task_actor : option nat) (eid : EventID)
  (allocation : EventPrivateAllocation) (count name : Z) : KernelClientAction :=
  event_create_publication_client task_actor eid allocation (sem_create_event allocation count name).

Lemma sem_create_publication_client_certificate : forall task_actor eid allocation count name,
  0 <= count <= 65535 -> allocation.(eventPrivateMutexPCP) = None ->
  KernelClientCertificate (sem_create_publication_client task_actor eid allocation count name).
Proof.
  intros task_actor eid allocation count name Hcount HnoMutexLease; apply event_create_publication_client_certificate;
    [reflexivity|discriminate|reflexivity|reflexivity|apply sem_create_event_fields_consistency| |exact HnoMutexLease].
  intro sg; apply sem_create_event_payload_consistency; exact Hcount.
Qed.
