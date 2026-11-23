Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_call_spec.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Immutable descriptor facts, extracted only after the four ordered public
    guards. The actual array ownership stays in the current full/missing view;
    this pure carrier does not create an output cell or require initialization. *)
Definition event_pend_multi_output_limits (ready messages : addr) (pointers : list addr)
  (old_ready old_messages : EventPendMultiSlots) : Prop :=
  0 < Zlength pointers /\
  Zlength pointers + 1 <= Zlength old_ready /\
  Zlength pointers <= Zlength old_messages /\
  0 < ready /\ ready + 4 * Zlength old_ready <= 4294967296 /\
  0 < messages /\ messages + 4 * Zlength old_messages <= 4294967296.

Lemma event_pend_multi_output_input_split_limits :
  forall ready messages pointers old_ready old_messages,
  0 < Zlength pointers -> ready <> 0 -> messages <> 0 ->
  event_pend_multi_output_input ready messages pointers old_ready old_messages |--
  “ event_pend_multi_output_limits ready messages pointers old_ready old_messages ” &&
  (event_pend_multi_output_rep ready old_ready **
   event_pend_multi_output_rep messages old_messages).
Proof.
  intros ready messages pointers old_ready old_messages Hlength Hready Hmessages.
  destruct pointers as [|pointer pointers]; [rewrite Zlength_nil in Hlength; lia|].
  cbn [event_pend_multi_output_input].
  destruct (Z.eq_dec ready 0); [contradiction|].
  destruct (Z.eq_dec messages 0); [contradiction|].
  unfold event_pend_multi_output_rep; Intros.
  assert (Hlimits : event_pend_multi_output_limits ready messages
    (pointer :: pointers) old_ready old_messages).
  { unfold event_pend_multi_output_limits; tauto. }
  entailer!.
Qed.

Definition event_pend_multi_validation_complete (state : UCOS2_Verify_State)
  (ids : list EventID) : Prop :=
  event_pend_multi_types_valid state.(EventState) ids = true.

(** Completion records the entry snapshot only. It is not a claim that these
    Event objects remain live or retain their type across Save/scheduling. *)
Lemma event_pend_multi_validation_loop_complete : forall sg state base pointers ids index,
  event_task_wait_multi_pointer pointers index = 0 ->
  event_pend_multi_validation_loop sg state pointers ids index **
  event_multi_array_rep base pointers |--
  “ event_pend_multi_validation_complete state ids ” &&
  (event_pend_multi_validation_loop sg state pointers ids index **
   event_multi_array_rep base pointers).
Proof.
  intros sg state base pointers ids index Hnull.
  unfold event_pend_multi_validation_loop, event_multi_array_rep; Intros.
  assert (Harray : event_multi_array_valid base pointers) by tauto.
  assert (Hids : event_pend_multi_ids_valid sg pointers ids) by tauto.
  assert (Hbounds : 0 <= index <= Zlength pointers) by tauto.
  assert (Hprefix : event_pend_multi_types_valid state.(EventState)
    (firstn (Z.to_nat index) ids) = true) by tauto.
  assert (Hlength : Zlength pointers = Zlength ids).
  { destruct Hids as [Hp Hvalid]; rewrite Hp, !Zlength_correct, List.length_map; reflexivity. }
  assert (Hend : index = Zlength pointers).
  { apply (proj1 (event_multi_array_null_iff_end base pointers index Harray Hbounds)); exact Hnull. }
  rewrite Hend, Hlength, Zlength_correct, Nat2Z.id, firstn_all in Hprefix.
  unfold event_pend_multi_validation_complete; entailer!.
Qed.

Definition event_pend_multi_precritical_success (state : UCOS2_Verify_State)
  (ids : list EventID) : Prop := event_pend_multi_precritical_error state ids = None.

Lemma event_pend_multi_precritical_success_from_guards : forall state ids,
  event_pend_multi_validation_complete state ids ->
  state.(IntrState).(intNesting) <= 0 -> state.(IntrState).(lockNesting) <= 0 ->
  event_pend_multi_precritical_success state ids.
Proof.
  intros state ids Htypes Hint Hlock.
  unfold event_pend_multi_validation_complete in Htypes.
  unfold event_pend_multi_precritical_success, event_pend_multi_precritical_error.
  rewrite Htypes; cbn [negb].
  assert (Hi : (0 <? intNesting (IntrState state)) = false) by (apply Z.ltb_ge; lia).
  assert (Hl : (0 <? lockNesting (IntrState state)) = false) by (apply Z.ltb_ge; lia).
  rewrite Hi, Hl; reflexivity.
Qed.
