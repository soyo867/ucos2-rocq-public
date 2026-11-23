Require Export Ucos2Verify.VC.code.tick.spec.app_time_tick_hook_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_signal_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** These observations reuse the existing full-u16 source transformer.
    The counter is a real port-private cell, not a new UCOS2 projection. *)
Definition time_tick_hook_advanced (counter : Z) : Z := kernel_u16 (counter + 1).
Definition time_tick_hook_counter_after (counter : Z) : Z :=
  fst (time_tick_hook_counter_step counter).
Definition time_tick_hook_signals (counter : Z) : bool :=
  snd (time_tick_hook_counter_step counter).

Lemma time_tick_hook_advanced_unsigned : forall counter,
  unsigned_last_nbits (counter + 1) 16 = time_tick_hook_advanced counter.
Proof. intros; unfold time_tick_hook_advanced, unsigned_last_nbits, kernel_u16; reflexivity. Qed.

Lemma time_tick_hook_signal_guard : forall counter,
  10 <= time_tick_hook_advanced counter -> time_tick_hook_signals counter = true.
Proof.
  intros counter H; unfold time_tick_hook_signals, time_tick_hook_counter_step.
  change (snd (if 10 <=? time_tick_hook_advanced counter then (0, true)
    else (time_tick_hook_advanced counter, false)) = true).
  rewrite (proj2 (Z.leb_le _ _) H); reflexivity.
Qed.

Lemma time_tick_hook_no_signal_guard : forall counter,
  time_tick_hook_advanced counter < 10 -> time_tick_hook_signals counter = false.
Proof.
  intros counter H; unfold time_tick_hook_signals, time_tick_hook_counter_step.
  change (snd (if 10 <=? time_tick_hook_advanced counter then (0, true)
    else (time_tick_hook_advanced counter, false)) = false).
  rewrite (proj2 (Z.leb_gt _ _) H); reflexivity.
Qed.

Lemma time_tick_hook_counter_after_signal : forall counter,
  time_tick_hook_signals counter = true -> time_tick_hook_counter_after counter = 0.
Proof.
  intros counter H; unfold time_tick_hook_signals, time_tick_hook_counter_after,
    time_tick_hook_counter_step in *.
  destruct (100 / 10 <=? kernel_u16 (counter + 1)); [reflexivity|discriminate].
Qed.

Lemma time_tick_hook_counter_after_no_signal : forall counter,
  time_tick_hook_signals counter = false ->
  time_tick_hook_counter_after counter = time_tick_hook_advanced counter.
Proof.
  intros counter H; unfold time_tick_hook_signals, time_tick_hook_counter_after,
    time_tick_hook_counter_step in *.
  destruct (100 / 10 <=? kernel_u16 (counter + 1)); [discriminate|reflexivity].
Qed.

(** Only the real signal branch asks for the delivered callee's handle
    and scheduling protocol. A no-signal return needs no readable ECB. *)
Definition time_tick_hook_call_inputs environment critical sg caller mask
  counter before eid observed : Prop :=
  time_tick_hook_signals counter = true ->
  tmr_signal_profile sg /\ UCOS2_state_inv sg before /\
  sem_post_api_call_input critical sg caller (tmr_signal_pointer before) before eid observed /\
  tmr_signal_optional_event_layout sg (tmr_signal_pointer before) eid /\
  sem_post_api_schedule_protocol environment critical sg caller mask
    (tmr_signal_pointer before) eid before.

Definition time_tick_hook_signal_continuation
  (X : UCOS2_Verify_State -> Prop) : Z -> UCOS2_Verify_State -> Prop :=
  fun _ state => X state.

Definition time_tick_hook_call_program environment critical sg caller mask eid counter
  : program UCOS2_Verify_State unit :=
  if time_tick_hook_signals counter then
    bind (tmr_signal_program environment critical sg caller mask eid)
      (fun _ => StateRelMonad.ret tt)
  else StateRelMonad.ret tt.

Definition time_tick_hook_safe environment critical sg caller mask eid counter before
  (X : UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (time_tick_hook_call_program environment critical sg caller mask eid counter)
    (fun _ state => X state).

Definition time_tick_hook_return_safe current (X : UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret tt) (fun _ state => X state).

Definition time_tick_hook_caller_result environment critical sg caller mask eid counter before
  returned current : Prop :=
  if time_tick_hook_signals counter then
    exists error, sem_post_api_caller_result environment critical sg caller mask
      (tmr_signal_pointer before) eid before error returned current
  else returned = caller /\ current = before.

Definition time_tick_hook_frame environment critical saved_local sg caller mask
  counter_address counter before : Assertion :=
  counter_address # UShort |-> counter **
  q_post_closed environment critical saved_local sg caller mask before.

Definition time_tick_hook_post environment critical saved_local sg caller mask eid
  counter_address counter before (X : UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (time_tick_hook_caller_result environment critical sg caller mask eid
      counter before returned current /\ time_tick_hook_return_safe current X) &&
    time_tick_hook_frame environment critical saved_local sg returned mask
      counter_address (time_tick_hook_counter_after counter) current.

Lemma time_tick_hook_signal_safe : forall environment critical sg caller mask eid counter before X,
  time_tick_hook_signals counter = true ->
  time_tick_hook_safe environment critical sg caller mask eid counter before X ->
  tmr_signal_safe environment critical sg caller mask eid before (time_tick_hook_signal_continuation X).
Proof.
  intros environment critical sg caller mask eid counter before X Hsignal Hsafe.
  unfold time_tick_hook_safe, time_tick_hook_call_program in Hsafe; rewrite Hsignal in Hsafe.
  unfold tmr_signal_safe.
  change (exists state, state = before /\
    forall error current, tmr_signal_program environment critical sg caller mask eid state error current ->
      X current).
  change (exists state, state = before /\
    forall result current,
      StateRelMonad.bind (tmr_signal_program environment critical sg caller mask eid)
        (fun _ => StateRelMonad.ret tt) state result current -> X current) in Hsafe.
  destruct Hsafe as [state [-> Hsafe]]; exists before; split; [reflexivity|].
  intros error current Hcall; apply (Hsafe tt current).
  exists error, current; split; [exact Hcall|split; reflexivity].
Qed.

Lemma time_tick_hook_no_signal_safe : forall environment critical sg caller mask eid counter before X,
  time_tick_hook_signals counter = false ->
  time_tick_hook_safe environment critical sg caller mask eid counter before X ->
  time_tick_hook_return_safe before X.
Proof.
  intros environment critical sg caller mask eid counter before X Hsignal Hsafe.
  unfold time_tick_hook_safe, time_tick_hook_call_program in Hsafe; rewrite Hsignal in Hsafe.
  exact Hsafe.
Qed.

Lemma time_tick_hook_signal_return_safe : forall current error X,
  q_post_return_safe current error (time_tick_hook_signal_continuation X) ->
  time_tick_hook_return_safe current X.
Proof.
  intros current error X Hsafe.
  change (exists state, state = current /\
    forall result final, StateRelMonad.ret error state result final -> X final) in Hsafe.
  change (exists state, state = current /\
    forall result final, StateRelMonad.ret tt state result final -> X final).
  destruct Hsafe as [state [-> Hsafe]]; exists current; split; [reflexivity|].
  intros result final [_ <-]; apply (Hsafe error current); split; reflexivity.
Qed.

Lemma time_tick_hook_result_program : forall environment critical sg caller mask eid counter before returned current,
  time_tick_hook_caller_result environment critical sg caller mask eid counter before returned current ->
  time_tick_hook_call_program environment critical sg caller mask eid counter before tt current.
Proof.
  intros environment critical sg caller mask eid counter before returned current Hresult.
  unfold time_tick_hook_caller_result in Hresult; unfold time_tick_hook_call_program.
  destruct (time_tick_hook_signals counter) eqn:Hsignal.
  - destruct Hresult as [error [prefix_caller [restored [schedule [Hprefix Htail]]]]].
    exists error, current; split; [|split; reflexivity].
    apply tmr_signal_program_iff.
    destruct schedule.
    + eapply sem_post_api_program_schedule; eassumption.
    + destruct Htail as [-> ->]; eapply sem_post_api_program_nonschedule; exact Hprefix.
  - destruct Hresult as [-> ->]; split; reflexivity.
Qed.

Lemma time_tick_hook_signal_return : forall environment critical saved_local sg caller mask eid
  counter_address counter before error X,
  time_tick_hook_signals counter = true ->
  counter_address # UShort |-> 0 **
  tmr_signal_post environment critical saved_local sg caller mask eid before error
    (time_tick_hook_signal_continuation X) |--
  time_tick_hook_post environment critical saved_local sg caller mask eid
    counter_address counter before X.
Proof.
  intros environment critical saved_local sg caller mask eid counter_address counter before error X Hsignal.
  unfold tmr_signal_post, sem_post_api_post; Intros returned current.
  match goal with H : _ /\ q_post_return_safe current error _ |- _ =>
    destruct H as [Hresult Hsafe]
  end.
  pose proof (time_tick_hook_signal_return_safe current error X Hsafe) as Hreturn.
  assert (Hcaller : time_tick_hook_caller_result environment critical sg caller mask eid
    counter before returned current).
  { unfold time_tick_hook_caller_result; rewrite Hsignal; exists error; exact Hresult. }
  unfold time_tick_hook_post, time_tick_hook_frame.
  rewrite (time_tick_hook_counter_after_signal counter Hsignal).
  Exists returned current.
  intros heap [frame_heap [counter_heap [Hjoin [Hframe Hcounter]]]].
  split; [exact (conj Hcaller Hreturn)|].
  exists counter_heap, frame_heap; split.
  - apply UCOS2_C_Rules.join_comm; exact Hjoin.
  - split; assumption.
Qed.

Lemma time_tick_hook_no_signal_return : forall environment critical saved_local sg caller mask eid
  counter_address counter before X,
  time_tick_hook_signals counter = false ->
  time_tick_hook_safe environment critical sg caller mask eid counter before X ->
  time_tick_hook_frame environment critical saved_local sg caller mask
    counter_address (time_tick_hook_advanced counter) before |--
  time_tick_hook_post environment critical saved_local sg caller mask eid
    counter_address counter before X.
Proof.
  intros environment critical saved_local sg caller mask eid counter_address counter before X Hsignal Hsafe.
  pose proof (time_tick_hook_no_signal_safe _ _ _ _ _ _ _ _ _ Hsignal Hsafe) as Hreturn.
  assert (Hcaller : time_tick_hook_caller_result environment critical sg caller mask eid
    counter before caller before).
  { unfold time_tick_hook_caller_result; rewrite Hsignal; split; reflexivity. }
  unfold time_tick_hook_post.
  rewrite (time_tick_hook_counter_after_no_signal counter Hsignal).
  Exists caller before.
  intros heap Hframe; split.
  - exact (conj Hcaller Hreturn).
  - exact Hframe.
Qed.

(** The real counter owner survives the callee as a separating resource.
    This post packages the same descriptor/current used by safeExec; it
    makes no Running/control promise about arbitrary registered intervals. *)
Lemma time_tick_hook_post_program : forall environment critical saved_local sg caller mask eid
  counter_address counter before X,
  time_tick_hook_post environment critical saved_local sg caller mask eid
    counter_address counter before X |--
  EX returned current,
    coq_prop (time_tick_hook_call_program environment critical sg caller mask eid counter
      before tt current /\ time_tick_hook_return_safe current X) &&
    time_tick_hook_frame environment critical saved_local sg returned mask
      counter_address (time_tick_hook_counter_after counter) current.
Proof.
  intros environment critical saved_local sg caller mask eid counter_address counter before X.
  unfold time_tick_hook_post.
  intros heap [returned [current [[Hresult Hsafe] Hframe]]].
  pose proof (time_tick_hook_result_program _ _ _ _ _ _ _ _ _ _ Hresult) as Hprogram.
  exists returned, current; split.
  - exact (conj Hprogram Hsafe).
  - exact Hframe.
Qed.

