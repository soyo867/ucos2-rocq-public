Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.VC.code.event.spec.event_name_spec.
Require Export Ucos2Verify.VC.code.core.spec.os_strlen_spec.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(**
    The public entry has four early guards, but only the default and the
    successful switch arms need an ECB/output focus.  Keep that focus opaque
    while the guards are being selected; the C annotation opens it at the
    corresponding arm with a local [which implies].  This is deliberately a
    field slice, not a second ECB representation: all fields not listed here
    stay in the caller frame.
*)
Definition event_name_get_type_focus
  (type_addr : addr) (type_byte : Z) : Assertion :=
  type_addr # UChar |-> type_byte.

Definition event_name_get_invalid_focus
  (pname : addr) (output_old : Z) : Assertion :=
  pname # Ptr |-> output_old.

(** A stored NULL name is not the NULL output-argument error.  The source
    stores it in [*pname] and the checked callee returns zero without a read. *)
Definition event_name_get_name_bytes (name : addr) (chars : list Z) : Assertion :=
  if Z.eqb name 0 then emp else os_strlen_bytes name chars.

Definition event_name_get_readable (names : NameResourceState)
  (name : addr) (chars : list Z) : Prop :=
  name <> 0 -> readable_name names name chars.

Definition event_name_get_length (name : addr) (chars : list Z) : Z :=
  if Z.eqb name 0 then 0 else name_length_result chars.

Definition event_name_get_result (names : NameResourceState)
  (name : addr) (chars : list Z) (len : Z) : Prop :=
  event_name_get_readable names name chars /\ len = event_name_get_length name chars.

Definition event_name_get_success_focus
  (name_addr pname name : addr) (output_old : Z)
  (chars : list Z) : Assertion :=
  (name_addr # Ptr |-> name) **
  (pname # Ptr |-> output_old) **
  event_name_get_name_bytes name chars.

(** The branch focus is a configuration-free selector for the concrete
    type-byte guard.  Keeping the boolean choice inside the Rocq owner avoids
    placing the four concrete type equalities in the C annotation's spatial
    disjunction; the selector still expands to the exact invalid/supported
    cells when its bridge lemmas are used.  It does not create permission or
    a second Event representation. *)
Definition event_name_get_branch_focus
  (type_addr name_addr pname name : addr) (type_byte output_old : Z)
  (chars : list Z) : Assertion :=
  event_name_get_type_focus type_addr type_byte **
  (if event_name_type_allowed type_byte
   then event_name_get_success_focus name_addr pname name output_old chars
   else event_name_get_invalid_focus pname output_old).

Definition event_name_get_branch_post_focus
  (type_addr name_addr pname name : addr) (type_byte output_old : Z)
  (chars : list Z) : Assertion :=
  event_name_get_type_focus type_addr type_byte **
  (if event_name_type_allowed type_byte
   then (name_addr # Ptr |-> name) **
        (pname # Ptr |-> name) ** event_name_get_name_bytes name chars
   else pname # Ptr |-> output_old).

Lemma event_name_get_type_focus_open : forall type_addr type_byte,
  event_name_get_type_focus type_addr type_byte |--
    type_addr # UChar |-> type_byte.
Proof. intros; unfold event_name_get_type_focus; entailer!. Qed.

Lemma event_name_get_invalid_focus_open : forall pname output_old,
  event_name_get_invalid_focus pname output_old |--
    pname # Ptr |-> output_old.
Proof. intros; unfold event_name_get_invalid_focus; entailer!. Qed.

Lemma event_name_get_success_focus_open : forall name_addr pname name output_old chars,
  event_name_get_success_focus name_addr pname name output_old chars |--
    (name_addr # Ptr |-> name) **
    (pname # Ptr |-> output_old) **
    event_name_get_name_bytes name chars.
Proof. intros; unfold event_name_get_success_focus; entailer!. Qed.

Lemma event_name_get_success_focus_close : forall name_addr pname name output_old chars,
  (name_addr # Ptr |-> name) **
    (pname # Ptr |-> output_old) **
    event_name_get_name_bytes name chars |--
  event_name_get_success_focus name_addr pname name output_old chars.
Proof. intros; unfold event_name_get_success_focus; entailer!. Qed.

Lemma event_name_get_branch_focus_open : forall type_addr name_addr pname name type_byte output_old chars,
  event_name_get_branch_focus type_addr name_addr pname name type_byte output_old chars |--
  event_name_get_type_focus type_addr type_byte **
  (if event_name_type_allowed type_byte
   then event_name_get_success_focus name_addr pname name output_old chars
   else event_name_get_invalid_focus pname output_old).
Proof. intros; unfold event_name_get_branch_focus; entailer!. Qed.

Lemma event_name_get_branch_focus_invalid : forall type_addr name_addr pname name type_byte output_old chars,
  event_name_type_allowed type_byte = false ->
  event_name_get_branch_focus type_addr name_addr pname name type_byte output_old chars |--
  event_name_get_type_focus type_addr type_byte **
  event_name_get_invalid_focus pname output_old.
Proof.
  intros; unfold event_name_get_branch_focus; rewrite H; entailer!.
Qed.

Lemma event_name_get_branch_focus_success : forall type_addr name_addr pname name type_byte output_old chars,
  event_name_type_allowed type_byte = true ->
  event_name_get_branch_focus type_addr name_addr pname name type_byte output_old chars |--
  event_name_get_type_focus type_addr type_byte **
  event_name_get_success_focus name_addr pname name output_old chars.
Proof.
  intros; unfold event_name_get_branch_focus; rewrite H; entailer!.
Qed.

(** OSEventNameGet's public observations: the error byte, INT8U return,
    and whether the caller's pointer output was written.  None means no
    write, not a null name.  OS_StrLen sees the bytes only on success. *)
Definition event_name_get_observation (names : NameResourceState)
  (pevent pname nesting type_byte name : Z) (chars : list Z)
  (error len : Z) (output : option addr) : Prop :=
  match event_name_get_error pevent pname nesting type_byte with
  | Some expected =>
      error = encode_os_err_code expected /\ len = 0 /\ output = None
  | None =>
      error = encode_os_err_code OS_ERR_NONE /\
      event_name_get_result names name chars len /\
      output = Some name
  end.

(** This is the operation at a stable observation point.  Environment
    interference before Save/after Restore is not equated with this identity
    step.  A concurrent client must compose it with its region protocol. *)
Definition event_name_get_sem (sg : StableGlobVars) (eid : EventID)
  (pevent pname nesting type_byte : Z)
  : program UCOS2_Verify_State (Z * (Z * option addr)) :=
  fun s result after =>
    after = s /\
    match event_name_get_error pevent pname nesting type_byte with
    | Some expected =>
        result = (0, (encode_os_err_code expected, None))
    | None => exists old chars,
        s.(EventState).(inUsedEventStates) eid = Some old /\
        pevent = event_addr sg eid /\
        type_byte = encode_event_type old.(eventType) /\
        event_name_get_readable s.(NameState) old.(eventName) chars /\
        result = (event_name_get_length old.(eventName) chars,
                  (encode_os_err_code OS_ERR_NONE, Some old.(eventName)))
    end.

Lemma event_name_get_sem_state_eq : forall sg eid pevent pname nesting ty s result after,
  event_name_get_sem sg eid pevent pname nesting ty s result after -> after = s.
Proof. intros; exact (proj1 H). Qed.

Lemma event_name_get_observation_error : forall names pevent pname nesting ty name chars err len output expected,
  event_name_get_error pevent pname nesting ty = Some expected ->
  event_name_get_observation names pevent pname nesting ty name chars err len output ->
  err = encode_os_err_code expected /\ len = 0 /\ output = None.
Proof. intros; unfold event_name_get_observation in H0; rewrite H in H0; exact H0. Qed.

Lemma event_name_get_observation_success : forall names pevent pname nesting ty name chars err len output,
  event_name_get_error pevent pname nesting ty = None ->
  event_name_get_observation names pevent pname nesting ty name chars err len output ->
  err = encode_os_err_code OS_ERR_NONE /\
  len = event_name_get_length name chars /\ output = Some name.
Proof.
  intros; unfold event_name_get_observation in H0; rewrite H in H0.
  destruct H0 as [Herr [Hlength Houtput]]; split; [exact Herr|].
  split; [exact (proj2 Hlength)|exact Houtput].
Qed.

Lemma event_name_get_result_exact : forall names name chars len,
  name <> 0 -> os_strlen_length_valid chars ->
  event_name_get_result names name chars len ->
  len = Z.of_nat (List.length chars).
Proof.
  intros names name chars len Hname Hlength [_ Hlen].
  unfold event_name_get_length in Hlen.
  rewrite (proj2 (Z.eqb_neq name 0) Hname) in Hlen.
  rewrite Hlen; apply name_length_result_exact; exact Hlength.
Qed.
