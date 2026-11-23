Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_view_primitive_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** FlagPendInactiveViewPrimitive is provided by the same checked low-level
    completion module. Its effects existentially retain the actual completion;
    no Task normal/control/source property is assumed here. *)
Module FlagPendInactiveFirstProgram.
Import PrimitiveComponent PendPhaseCandidate FlagPendInactiveViewPrimitive.

Definition flag_pend_first_save_effect environment critical sg original mask saved
  before entered acquired : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect
    environment critical sg original mask saved before entered acquired \/
  flag_pend_inactive_save_effect environment critical sg original mask saved before entered acquired.

Definition flag_pend_first_restore_effect environment critical sg entered
  released returned current : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect
    environment critical sg entered released returned current \/
  flag_pend_inactive_restore_effect environment critical sg entered released returned current.

(** Only the original First=false path is added. The early tests and the
    actual invalid-mode critical result are retained. Save and Restore choose
    independently, so both mixed Task/view executions remain represented. *)
Definition flag_pend_inactive_first_program environment critical sg call mask
  (i pgrp requested wait_type timeout : Z) : program UCOS2_Verify_State (Z * Z) :=
  fun before result current =>
  ~ (flag_pend_valid_mode wait_type \/ flag_pend_task_entry call before) /\
  pgrp <> 0 /\ before.(IntrState).(intNesting) <= 0 /\
  before.(IntrState).(lockNesting) <= 0 /\
  exists observed entered saved acquired returned,
    before.(FlagState).(flagImages) i = Some observed /\ observed.(flagImageType) = 5 /\
    flag_pend_first_save_effect environment critical sg call mask saved before entered acquired /\
    flag_pend_first_critical sg i requested wait_type timeout
      acquired (FlagPendReturn 0 111) acquired /\
    flag_pend_first_restore_effect environment critical sg entered acquired returned current /\
    result = (0, 111).

Definition flag_pend_task_program environment critical sg call mask i pgrp requested wait_type timeout :
  program UCOS2_Verify_State (Z * Z) :=
  StateRelBasic.choice
    (PendPhaseCandidate.flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout)
    (flag_pend_inactive_first_program environment critical sg call mask i pgrp requested wait_type timeout).

Definition flag_pend_caller_program environment critical sg caller call mask
  i pgrp requested wait_type timeout :=
  match caller with
  | FlagPendTaskCaller _ =>
      flag_pend_task_program environment critical sg call mask i pgrp requested wait_type timeout
  | FlagPendInterruptCaller view _ =>
      PendPhaseCandidate.flag_pend_view_program critical sg view i pgrp requested wait_type timeout
  end.

Definition flag_pend_caller_safe environment critical sg caller call mask
  i pgrp requested wait_type timeout before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (flag_pend_caller_program environment critical sg caller call mask i pgrp requested wait_type timeout)
    (fun result state => X (fst result) (snd result) state).

(** The physical input domain is the original one. Only the source program
    interpreted by the same arbitrary X now includes the actual inactive calls. *)
Definition flag_pend_public_entry environment critical sg caller call mask
  i pgrp requested wait_type timeout before X : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  (pgrp = 0 \/ (0 <= i < sg.(osKernelConfig).(cfgMaxFlags) /\ pgrp = flag_pool_addr sg i)) /\
  0 <= requested < 65536 /\ 0 <= wait_type < 256 /\ 0 <= timeout < 4294967296 /\
  flag_pend_caller_source sg caller call i pgrp wait_type before /\
  flag_pend_caller_safe environment critical sg caller call mask i pgrp requested wait_type timeout before X.

(** The six existing entry-source constructors and their actual heap are
    unchanged. This is the public owned input with the new source safeExec. *)
Definition flag_pend_owned_input environment critical boundary local sg linked caller call mask
  i pgrp requested mode delay perr before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) (frame : Assertion) : Assertion :=
  fun heap =>
    flag_pend_entry_source environment critical boundary sg linked local caller call mask i pgrp mode before
      ((perr # UChar |->_) ** frame) heap /\
    sg.(osKernelConfig) = selected_kernel_configuration /\
    (pgrp = 0 \/ (0 <= i < sg.(osKernelConfig).(cfgMaxFlags) /\ pgrp = flag_pool_addr sg i)) /\
    0 <= requested < 65536 /\ 0 <= mode < 256 /\ 0 <= delay < 4294967296 /\
    flag_pend_caller_safe environment critical sg caller call mask i pgrp requested mode delay before X.

Lemma flag_pend_owned_input_open : forall environment critical boundary local sg linked caller call mask
  i pgrp requested mode delay perr before X frame,
  flag_pend_owned_input environment critical boundary local sg linked caller call mask
    i pgrp requested mode delay perr before X frame |--
  coq_prop (flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay before X) &&
    (flag_pend_caller_world environment local sg caller mask before ** (perr # UChar |->_) ** frame).
Proof.
  intros environment critical boundary local sg linked caller call mask i pgrp requested mode delay perr before X frame
    heap [Hsource Hargs].
  destruct (flag_pend_entry_source_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource) as [Hentry Hworld].
  assert (Hpublic : flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay before X).
  { unfold flag_pend_public_entry; tauto. }
  assert (Horder : flag_pend_caller_world environment local sg caller mask before **
    ((perr # UChar |->_) ** frame) |--
    coq_prop (flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay before X) &&
    (flag_pend_caller_world environment local sg caller mask before **
      (perr # UChar |->_) ** frame)) by entailer!.
  exact (Horder heap Hworld).
Qed.

Lemma flag_pend_first_save_effect_same_call :
  forall environment critical sg original mask saved before entered acquired,
  flag_pend_first_save_effect environment critical sg original mask saved before entered acquired ->
  task_tcb_init_stack_same_call entered original.
Proof.
  intros environment critical sg original mask saved before entered acquired [Htask|Hview].
  - eapply ContinuationPhaseEffects.os_sched_continuation_phase_save_effect_same_call; exact Htask.
  - exact (proj1 (flag_pend_inactive_save_effect_observations
      environment critical sg original mask saved before entered acquired Hview)).
Qed.

Lemma flag_pend_first_restore_effect_same_call :
  forall environment critical sg entered released returned current,
  flag_pend_first_restore_effect environment critical sg entered released returned current ->
  task_tcb_init_stack_same_call returned entered.
Proof.
  intros environment critical sg entered released returned current [Htask|Hview].
  - eapply ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect_same_call; exact Htask.
  - exact (proj1 (flag_pend_inactive_restore_effect_observations
      environment critical sg entered released returned current Hview)).
Qed.

Lemma flag_pend_first_effects_same_call :
  forall environment critical sg original mask saved before entered acquired released returned current,
  flag_pend_first_save_effect environment critical sg original mask saved before entered acquired ->
  flag_pend_first_restore_effect environment critical sg entered released returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg original mask saved before entered acquired released returned current Hsave Hrestore.
  pose proof (flag_pend_first_save_effect_same_call environment critical sg original mask saved
    before entered acquired Hsave) as Hsame_save.
  pose proof (flag_pend_first_restore_effect_same_call environment critical sg entered released
    returned current Hrestore) as Hsame_restore.
  unfold task_tcb_init_stack_same_call in *; intuition congruence.
Qed.

Lemma flag_pend_inactive_first_program_return :
  forall environment critical sg call mask i pgrp requested wait_type timeout
    before observed entered saved acquired returned current,
  ~ (flag_pend_valid_mode wait_type \/ flag_pend_task_entry call before) ->
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
  before.(FlagState).(flagImages) i = Some observed -> observed.(flagImageType) = 5 ->
  flag_pend_first_save_effect environment critical sg call mask saved before entered acquired ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn 0 111) acquired ->
  flag_pend_first_restore_effect environment critical sg entered acquired returned current ->
  flag_pend_inactive_first_program environment critical sg call mask i pgrp requested wait_type timeout
    before (0, 111) current.
Proof.
  intros environment critical sg call mask i pgrp requested wait_type timeout
    before observed entered saved acquired returned current Hfalse Hptr Hints Hlocks Himage Htype Hsave Hfirst Hrestore.
  split; [exact Hfalse|]. split; [exact Hptr|]. split; [exact Hints|]. split; [exact Hlocks|].
  exists observed, entered, saved, acquired, returned.
  exact (conj Himage (conj Htype (conj Hsave (conj Hfirst (conj Hrestore eq_refl))))).
Qed.

Lemma flag_pend_task_program_includes_original :
  forall environment critical sg call mask i pgrp requested wait_type timeout before result current,
  PendPhaseCandidate.flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout
    before result current ->
  flag_pend_task_program environment critical sg call mask i pgrp requested wait_type timeout
    before result current.
Proof. intros; left; assumption. Qed.

Lemma flag_pend_task_program_active_iff :
  forall environment critical sg call mask i pgrp requested wait_type timeout before result current,
  (flag_pend_valid_mode wait_type \/ flag_pend_task_entry call before) ->
  (flag_pend_task_program environment critical sg call mask i pgrp requested wait_type timeout
      before result current <->
   PendPhaseCandidate.flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout
      before result current).
Proof.
  intros environment critical sg call mask i pgrp requested wait_type timeout before result current Hactive.
  split.
  - intros [Hold|[Hfalse Hrest]]; [exact Hold|contradiction].
  - apply flag_pend_task_program_includes_original.
Qed.

Lemma flag_pend_caller_safe_restrict :
  forall environment critical sg caller call mask i pgrp requested wait_type timeout before X,
  flag_pend_caller_safe environment critical sg caller call mask i pgrp requested wait_type timeout before X ->
  PendPhaseCandidate.flag_pend_caller_safe environment critical sg caller call mask
    i pgrp requested wait_type timeout before X.
Proof.
  intros environment critical sg caller call mask i pgrp requested wait_type timeout before X Hsafe.
  destruct caller as [task_call|view key].
  - unfold flag_pend_caller_safe, flag_pend_caller_program, flag_pend_task_program in Hsafe.
    unfold PendPhaseCandidate.flag_pend_caller_safe, PendPhaseCandidate.flag_pend_caller_program.
    eapply safeExec_choice_l; exact Hsafe.
  - exact Hsafe.
Qed.

Lemma flag_pend_public_entry_restrict :
  forall environment critical sg caller call mask i pgrp requested wait_type timeout before X,
  flag_pend_public_entry environment critical sg caller call mask i pgrp requested wait_type timeout before X ->
  PendPhaseCandidate.flag_pend_public_entry environment critical sg caller call mask
    i pgrp requested wait_type timeout before X.
Proof.
  intros environment critical sg caller call mask i pgrp requested wait_type timeout before X
    [Hconfig [Haddress [Hrequested [Hmode [Htimeout [Hsource Hsafe]]]]]].
  exact (conj Hconfig (conj Haddress (conj Hrequested (conj Hmode (conj Htimeout
    (conj Hsource (flag_pend_caller_safe_restrict environment critical sg caller call mask
      i pgrp requested wait_type timeout before X Hsafe))))))).
Qed.

Lemma flag_pend_caller_program_inactive_return :
  forall environment critical sg call mask i pgrp requested wait_type timeout before current,
  flag_pend_inactive_first_program environment critical sg call mask i pgrp requested wait_type timeout
    before (0, 111) current ->
  flag_pend_caller_program environment critical sg (FlagPendTaskCaller call) call mask
    i pgrp requested wait_type timeout before (0, 111) current.
Proof. intros; right; assumption. Qed.

Lemma flag_pend_caller_safe_return :
  forall environment critical sg caller call mask i pgrp requested wait_type timeout
    before ready error current X,
  flag_pend_caller_program environment critical sg caller call mask i pgrp requested wait_type timeout
    before (ready, error) current ->
  flag_pend_caller_safe environment critical sg caller call mask i pgrp requested wait_type timeout before X ->
  flag_pend_return_safe ready error current X.
Proof.
  intros environment critical sg caller call mask i pgrp requested wait_type timeout
    before ready error current X Hstep Hsafe.
  unfold flag_pend_caller_safe in Hsafe; unfold flag_pend_return_safe.
  eapply (highstependret_derive
    (flag_pend_caller_program environment critical sg caller call mask i pgrp requested wait_type timeout)
    (fun state => state = before) (ready, error) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma flag_pend_caller_safe_inactive_return :
  forall environment critical sg call mask i pgrp requested wait_type timeout
    before observed entered saved acquired returned current X,
  ~ (flag_pend_valid_mode wait_type \/ flag_pend_task_entry call before) ->
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
  before.(FlagState).(flagImages) i = Some observed -> observed.(flagImageType) = 5 ->
  flag_pend_first_save_effect environment critical sg call mask saved before entered acquired ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn 0 111) acquired ->
  flag_pend_first_restore_effect environment critical sg entered acquired returned current ->
  flag_pend_caller_safe environment critical sg (FlagPendTaskCaller call) call mask
    i pgrp requested wait_type timeout before X ->
  flag_pend_return_safe 0 111 current X.
Proof.
  intros environment critical sg call mask i pgrp requested wait_type timeout
    before observed entered saved acquired returned current X Hfalse Hptr Hints Hlocks Himage Htype
    Hsave Hfirst Hrestore Hsafe.
  eapply flag_pend_caller_safe_return; [|exact Hsafe].
  apply flag_pend_caller_program_inactive_return.
  eapply flag_pend_inactive_first_program_return; eassumption.
Qed.

(** The actual callee's returned owner supplies this world, including its
    own next_local. The private caller frame remains outside this entailment. *)
Lemma flag_pend_inactive_first_public_post :
  forall environment critical local next_local sg call mask i pgrp requested wait_type timeout
    before observed entered saved acquired returned current perr X,
  flag_pend_public_entry environment critical sg (FlagPendTaskCaller call) call mask
    i pgrp requested wait_type timeout before X ->
  ~ (flag_pend_valid_mode wait_type \/ flag_pend_task_entry call before) ->
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
  before.(FlagState).(flagImages) i = Some observed -> observed.(flagImageType) = 5 ->
  flag_pend_first_save_effect environment critical sg call mask saved before entered acquired ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn 0 111) acquired ->
  flag_pend_first_restore_effect environment critical sg entered acquired returned current ->
  flag_pend_caller_world environment next_local sg (FlagPendTaskCaller returned) mask current **
    perr # UChar |-> 111 |--
  PendPhaseCandidate.flag_pend_public_post environment local sg (FlagPendTaskCaller call) call mask perr before 0 X.
Proof.
  intros environment critical local next_local sg call mask i pgrp requested wait_type timeout
    before observed entered saved acquired returned current perr X
    [Hconfig [Haddress [Hrequested [Hmode [Htimeout [Hsource Hsafe]]]]]]
    Hfalse Hptr Hints Hlocks Himage Htype Hsave Hfirst Hrestore.
  pose proof (flag_pend_caller_safe_inactive_return environment critical sg call mask i pgrp
    requested wait_type timeout before observed entered saved acquired returned current X
    Hfalse Hptr Hints Hlocks Himage Htype Hsave Hfirst Hrestore Hsafe) as Hreturn.
  pose proof (flag_pend_first_effects_same_call environment critical sg call mask saved
    before entered acquired acquired returned current Hsave Hrestore) as Hsame.
  intros heap Howned.
  exists (FlagPendTaskCaller returned), current, 111, next_local.
  split; [|exact Howned].
  split; [exact Hreturn|]. split; [exact Hsame|].
  split; [exact Hsame|]. intro Hentry; exfalso; apply Hfalse; right; exact Hentry.
Qed.

End FlagPendInactiveFirstProgram.

