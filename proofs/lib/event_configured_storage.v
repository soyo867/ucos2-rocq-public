Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.

Import ListNotations EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Configuration-owned Event storage vocabulary.  This is a selector over
    the existing names-disabled/names-enabled images, not a second Event
    representation. *)
Definition configured_event_named (sg : StableGlobVars) : bool :=
  sg.(osKernelConfig).(cfgEventNames).

Definition configured_event_stride (sg : StableGlobVars) : Z :=
  event_object_size sg.(osKernelConfig).

Definition configured_event_storage_rep (sg : StableGlobVars) (base : addr)
  (image : EventStorage) : Assertion :=
  event_storage_rep (configured_event_named sg) base image.

Definition configured_event_boot_image (sg : StableGlobVars)
  (ids : list EventID) (eid : EventID) (name : addr) : EventStorage :=
  if configured_event_named sg
  then event_boot_image_named sg ids eid name
  else event_boot_image sg ids eid.

Lemma configured_event_named_true : forall sg,
  configured_event_named sg = true -> configured_event_named sg = true.
Proof. intros; exact H. Qed.

Lemma configured_event_stride_legacy : forall sg,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  configured_event_stride sg = 20.
Proof.
  intros sg H; unfold configured_event_stride, event_object_size.
  rewrite H; reflexivity.
Qed.

Lemma configured_event_stride_named : forall sg,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  configured_event_stride sg = 24.
Proof.
  intros sg H; unfold configured_event_stride, event_object_size.
  rewrite H; reflexivity.
Qed.

Lemma configured_event_boot_image_legacy : forall sg ids eid name,
  configured_event_named sg = false ->
  configured_event_boot_image sg ids eid name = event_boot_image sg ids eid.
Proof. intros; unfold configured_event_boot_image; rewrite H; reflexivity. Qed.

Lemma configured_event_boot_image_named : forall sg ids eid name,
  configured_event_named sg = true ->
  configured_event_boot_image sg ids eid name = event_boot_image_named sg ids eid name.
Proof. intros; unfold configured_event_boot_image; rewrite H; reflexivity. Qed.
