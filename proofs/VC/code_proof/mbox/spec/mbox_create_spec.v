Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mbox.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.VC.code.event.spec.event_create_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** MboxCreate permits an initial NULL message.  Reuse the canonical
    pointer-to-message conversion; the ECB owns the pointer cell, not
    the application's pointed-to memory. *)
Definition mbox_create_private_initialization (sg : StableGlobVars)
  (eid : EventID) (message name : addr) :=
  event_create_private_initialization eid sg.(osKernelConfig).(cfgEventNames) 1 0 message name.

Definition mbox_create_event (allocation : EventPrivateAllocation) (message name : addr) : OSEventAbstractState :=
  {| eventGeneration := allocation.(eventPrivateGeneration);
     eventName := name; eventPadding1 := allocation.(eventPrivateStorage) EventPadding1;
     eventPadding2 := allocation.(eventPrivateStorage) EventPadding2; eventPadding3 := allocation.(eventPrivateStorage) EventPadding3;
     eventPadding19 := allocation.(eventPrivateStorage) EventPadding19;
     eventType := OS_EVENT_TYPE_MBOX; mutexFields := None; semFields := None;
     mboxFields := Some (mbox_message_from_ptr message); queueFields := None; waitList := [] |}.

Lemma mbox_create_event_fields_consistency : forall allocation message name,
  event_fields_consistency (mbox_create_event allocation message name).
Proof. intros; repeat split; discriminate. Qed.

Lemma mbox_create_event_payload_consistency : forall sg allocation message name,
  event_payload_consistency sg (mbox_create_event allocation message name).
Proof.
  intros sg allocation message name; split; [|intros H; contradiction].
  simpl; destruct (Z.eqb message 0) eqn:H;
    [exact I|apply Z.eqb_neq in H; exact H].
Qed.

Lemma mbox_create_image_matches_event : forall sg tasks allocation image message name,
  allocation.(eventPrivateStorage) = event_create_image sg.(osKernelConfig).(cfgEventNames) 1 0 message name image ->
  forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg tasks (mbox_create_event allocation message name) field.
Proof.
  intros sg tasks allocation image message name Himage field Hin;
    destruct sg.(osKernelConfig).(cfgEventNames); destruct field;
    try (exfalso; unfold event_fields in Hin; simpl in Hin; intuition discriminate);
    unfold event_image, mbox_create_event; rewrite Himage; try reflexivity.
  all: change (Some message = Some (mbox_message_ptr (mbox_message_from_ptr message)));
    rewrite mbox_message_ptr_from_ptr; reflexivity.
Qed.

Lemma mbox_create_publish_preserves_validity : forall sg s eid allocation message name,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_name_valid sg s.(NameState) (mbox_create_event allocation message name) ->
  allocation.(eventPrivateMutexPCP) = None ->
  UCOS2_state_inv sg
    (replace_EventS (event_publish s.(EventState) eid (mbox_create_event allocation message name)) s).
Proof.
  intros sg s eid allocation message name Hvalid Hget Hname HnoMutexLease.
  eapply UCOS2_event_publish_preserves_validity;
    [exact Hvalid|exact Hget|reflexivity|discriminate|reflexivity|reflexivity| | |exact Hname|exact HnoMutexLease].
  - apply mbox_create_event_fields_consistency.
  - apply mbox_create_event_payload_consistency.
Qed.

Lemma mbox_create_publish_merge : forall sg s eid allocation image message name,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  allocation.(eventPrivateStorage) = event_create_image sg.(osKernelConfig).(cfgEventNames) 1 0 message name image ->
  event_name_valid sg s.(NameState) (mbox_create_event allocation message name) ->
  allocation.(eventPrivateMutexPCP) = None ->
  event_private_storage_rep sg eid allocation **
    (event_raw_rep sg s.(TskState) s.(EventState) **
     queue_storage_rep sg s.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg s) |--
  UCOS2_inv sg
    (replace_EventS (event_publish s.(EventState) eid (mbox_create_event allocation message name)) s).
Proof.
  intros sg s eid allocation image message name Hvalid Hget Hqueue Himage Hname HnoMutexLease.
  eapply UCOS2_inv_merge_event_publish;
    [exact Hvalid|exact Hget|exact Hqueue| |reflexivity|discriminate|reflexivity|reflexivity| | |exact Hname|exact HnoMutexLease].
  - eapply mbox_create_image_matches_event; exact Himage.
  - apply mbox_create_event_fields_consistency.
  - apply mbox_create_event_payload_consistency.
Qed.

Definition mbox_create_publication_client (task_actor : option nat) (eid : EventID)
  (allocation : EventPrivateAllocation) (message name : addr) : KernelClientAction :=
  event_create_publication_client task_actor eid allocation (mbox_create_event allocation message name).

Lemma mbox_create_publication_client_certificate : forall task_actor eid allocation message name,
  allocation.(eventPrivateMutexPCP) = None ->
  KernelClientCertificate (mbox_create_publication_client task_actor eid allocation message name).
Proof.
  intros task_actor eid allocation message name HnoMutexLease; apply event_create_publication_client_certificate;
    [reflexivity|discriminate|reflexivity|reflexivity|apply mbox_create_event_fields_consistency| |exact HnoMutexLease].
  intro sg; apply mbox_create_event_payload_consistency.
Qed.
