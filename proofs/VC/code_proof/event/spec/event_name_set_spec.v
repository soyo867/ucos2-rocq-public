Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.VC.code.event.spec.event_name_spec.

Import UCOS2_C_Rules.
Import EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Branch focus for the source's ordered type switch.  The boolean selector
    is owned by [event_name_spec]; keeping it here avoids reproducing the
    concrete four-way type OR in the C spatial disjunction.  The supported
    branch carries the old/new EventName cell, while unsupported types carry
    no name cell. *)
Definition event_name_set_type_focus (type_addr : addr) (type_byte : Z) : Assertion :=
  type_addr # UChar |-> type_byte.

Definition event_name_set_branch_focus
  (type_addr name_addr : addr) (type_byte name_old : Z) : Assertion :=
  event_name_set_type_focus type_addr type_byte **
  (if event_name_type_allowed type_byte
   then name_addr # Ptr |-> name_old
   else emp).

Definition event_name_set_branch_post_focus
  (type_addr name_addr : addr) (type_byte name : Z) : Assertion :=
  event_name_set_type_focus type_addr type_byte **
  (if event_name_type_allowed type_byte
   then name_addr # Ptr |-> name
   else emp).

Lemma event_name_set_branch_focus_invalid : forall type_addr name_addr type_byte name_old,
  event_name_type_allowed type_byte = false ->
  event_name_set_branch_focus type_addr name_addr type_byte name_old |--
  event_name_set_type_focus type_addr type_byte.
Proof. intros; unfold event_name_set_branch_focus; rewrite H; entailer!. Qed.

Lemma event_name_set_branch_focus_supported : forall type_addr name_addr type_byte name_old,
  event_name_type_allowed type_byte = true ->
  event_name_set_branch_focus type_addr name_addr type_byte name_old |--
  event_name_set_type_focus type_addr type_byte **
    (name_addr # Ptr |-> name_old).
Proof. intros; unfold event_name_set_branch_focus; rewrite H; entailer!. Qed.

Lemma event_name_set_branch_post_focus_supported : forall type_addr name_addr type_byte name,
  event_name_type_allowed type_byte = true ->
  event_name_set_branch_post_focus type_addr name_addr type_byte name |--
  event_name_set_type_focus type_addr type_byte **
    (name_addr # Ptr |-> name).
Proof. intros; unfold event_name_set_branch_post_focus; rewrite H; entailer!. Qed.

(** Public OSEventNameSet uses an exclusive-cell contract.  The complete
    ECB/global-region refinement is intentionally a separate integration
    obligation; these predicates only expose cells the C body accesses. *)
Definition event_name_set_observation (pevent pname : addr)
  (nesting type_byte error : Z) : Prop :=
  match event_name_set_error pevent pname nesting type_byte with
  | Some expected => error = encode_os_err_code expected
  | None => error = encode_os_err_code OS_ERR_NONE
  end.

Lemma event_name_set_observation_expected : forall pevent pname nesting type_byte error,
  event_name_set_observation pevent pname nesting type_byte error ->
  match event_name_set_error pevent pname nesting type_byte with
  | Some expected => error = encode_os_err_code expected
  | None => error = encode_os_err_code OS_ERR_NONE
  end.
Proof. intros; exact H. Qed.

(** The source updates only the EventName pointer.  With the names-enabled
    profile, [event_rep_merge_updated_name] is the reusable bridge from the
    focused pointer cell and the non-name ECB residual to the configured ECB
    image.  It is intentionally not pulled into the public precondition: the
    exclusive-cell candidate does not yet claim a global map ownership proof. *)
Lemma event_name_set_updated_name_cell_merge : forall sg tasks eid old name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  (event_addr sg eid + 20) # Ptr |-> name **
    event_rep_no_name sg tasks eid old |--
    used_event_rep sg tasks eid (event_set_name old name).
Proof.
  intros; apply event_rep_merge_updated_name; assumption.
Qed.

(** Queue storage is a non-target frame for NameSet: the EventName update
    preserves the queue payload/type projections consumed by the existing
    queue owner.  This is the cross-module spatial bridge; it does not claim
    the full Event map or name-byte ownership. *)
Lemma event_name_set_queue_storage_frame : forall sg events eid old name,
  events.(inUsedEventStates) eid = Some old ->
  queue_storage_rep sg events |--
    queue_storage_rep sg
      (update_event_field_raw events eid (event_set_name old name)).
Proof.
  intros sg events eid old name Hget.
  eapply queue_event_update_preserves_storage
    with (old := old) (new := event_set_name old name);
    [exact Hget|reflexivity|reflexivity].
Qed.
