Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_heap_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_loop_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_call_pend_view_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Import ListNotations.
Local Open Scope Z_scope.

Definition tmr_task_client_pend_lifted_post environment critical sg call mask pevent timeout perr before X :=
  TmrTaskFieldsRules.lift (tmr_task_client_pend_post environment critical sg call mask
    pevent timeout perr before X).

Definition tmr_task_client_pend_argument_rest environment local critical sg call mask
  signal timeout perr before eid observed X signal_address :=
  TmrTaskFieldsRules.wand (TmrTaskFieldsRules.store_ptr signal_address signal)
    (TmrTaskFieldsRules.lift (tmr_task_client_pend_pre environment local critical sg call mask
      signal timeout perr before eid observed X)).

Definition tmr_task_client_pend_argument_pre environment local critical sg call mask
  signal timeout perr before eid observed X signal_address :=
  TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.store_ptr signal_address signal)
    (tmr_task_client_pend_argument_rest environment local critical sg call mask
      signal timeout perr before eid observed X signal_address).

Lemma tmr_task_client_pend_argument_closed : forall environment local critical sg call mask
  signal timeout perr before eid observed X signal_address,
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_pend_argument_pre environment local critical sg call mask
      signal timeout perr before eid observed X signal_address)
    (TmrTaskFieldsRules.lift (tmr_task_client_pend_pre environment local critical sg call mask
      signal timeout perr before eid observed X)).
Proof.
  intros environment local critical sg call mask signal timeout perr before eid observed X
    signal_address heap [cell [rest [Hjoin [Hcell Hrest]]]].
  apply (Hrest cell heap).
  - exact (TmrTaskFieldsRules.join_comm cell rest heap Hjoin).
  - exact Hcell.
Qed.

Lemma tmr_task_client_pend_profile_enabled : forall sg,
  tmr_task_profile sg -> sg.(osKernelConfig).(cfgTimerEnabled) = true.
Proof. intros sg H; unfold tmr_task_profile, tmr_link_profile in H; tauto. Qed.

Module TmrTaskClientPendHeap.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Definition timer_without_signal sg timers : Assertion :=
  timer_images_rep sg timers **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) **
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg timers.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> timers.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> timers.(timerUsedCount) **
  sg.(g_OSTmrTime) # UInt |-> timers.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> timers.(timerSem).

Lemma timer_split_merge_signal : forall sg timers,
  timer_raw_rep sg timers --||--
  sg.(g_OSTmrSemSignal) # Ptr |-> timers.(timerSignalSem) ** timer_without_signal sg timers.
Proof.
  intros; unfold timer_raw_rep, timer_globals_rep, timer_without_signal; split; entailer!.
Qed.

Definition signal_rest environment local sg call mask perr before : Assertion :=
  TmrTaskFieldsHeap.context_rest environment local sg call mask before
    (timer_without_signal sg before.(TimerState)) ** sem_pend_error_cell perr.

Lemma signal_rest_closes_pend : forall environment local critical sg call mask perr before
  eid observed,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(TimerState) ->
  sem_pend_fields_call_domain environment critical sg call before.(TimerState).(timerSignalSem)
    before eid observed ->
  tmr_task_client_pend_entry sg call before ->
  signal_rest environment local sg call mask perr before |--
  (sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) -*
    tmr_task_client_pend_pre environment local critical sg call mask
      before.(TimerState).(timerSignalSem) 0 perr before eid observed tmr_task_legacy_any).
Proof.
  intros environment local critical sg call mask perr before eid observed Hen Hinit Hdomain Hentry.
  apply_sepcon_adjoint.
  assert (Hmerge :
    signal_rest environment local sg call mask perr before **
      sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) |--
    sem_pend_error_cell perr ** TmrTaskFields.tmr_task_fields_context environment local sg call mask before).
  { sep_apply_r_atomic (TmrTaskFieldsHeap.context_merge_read_part environment local sg call mask before
      (TmrTaskFieldsHeap.cell TaskPointerCell sg.(g_OSTmrSemSignal) before.(TimerState).(timerSignalSem))
      (timer_without_signal sg before.(TimerState)) Hen Hinit
      (proj2 (timer_split_merge_signal sg before.(TimerState)))).
    unfold signal_rest, TmrTaskFieldsHeap.cell; entailer!. }
  intros heap Hheap; split.
  - split; [exact Hdomain|]. split; [exact Hentry|].
    unfold sem_pend_client_fields_call_safe, safeExec, safe, StateRelHoare.weakestpre, tmr_task_legacy_any.
    exists (RTrans_Abs before); split.
    + unfold LastSeen; intro state; split; trivial.
    + sets_unfold; intros; exact I.
  - exact (Hmerge heap Hheap).
Qed.

Lemma context_split_pend_argument : forall environment local critical sg call mask perr before
  eid observed,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(TimerState) ->
  sem_pend_fields_call_domain environment critical sg call before.(TimerState).(timerSignalSem)
    before eid observed ->
  tmr_task_client_pend_entry sg call before ->
  TmrTaskFields.tmr_task_fields_context environment local sg call mask before ** sem_pend_error_cell perr |--
  sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) **
    (sg.(g_OSTmrSemSignal) # Ptr |-> before.(TimerState).(timerSignalSem) -*
      tmr_task_client_pend_pre environment local critical sg call mask
        before.(TimerState).(timerSignalSem) 0 perr before eid observed tmr_task_legacy_any).
Proof.
  intros environment local critical sg call mask perr before eid observed Hen Hinit Hdomain Hentry.
  sep_apply_l_atomic (TmrTaskFieldsHeap.context_split_part environment local sg call mask before
    (TmrTaskFieldsHeap.cell TaskPointerCell sg.(g_OSTmrSemSignal) before.(TimerState).(timerSignalSem))
    (timer_without_signal sg before.(TimerState)) Hen Hinit
    (proj1 (timer_split_merge_signal sg before.(TimerState)))).
  sep_apply_r_atomic (signal_rest_closes_pend environment local critical sg call mask perr before
    eid observed Hen Hinit Hdomain Hentry).
  unfold signal_rest, TmrTaskFieldsHeap.cell; entailer!.
Qed.

End TmrTaskClientPendHeap.

Lemma tmr_task_client_pend_argument_from_owner : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical sg call mask perr
  (world : tmr_task_scan_world Application) eid observed,
  tmr_task_profile sg -> timer_api_initialized (tmr_task_timers world) ->
  sem_pend_fields_call_domain environment critical sg call
    (tmr_task_timers world).(timerSignalSem) (tmr_task_kernel world) eid observed ->
  tmr_task_client_pend_entry sg call (tmr_task_kernel world) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world)
    (fun heap => exists local,
      TmrTaskFieldsRules.sepcon
        (tmr_task_client_pend_argument_pre environment local critical sg call mask
          (tmr_task_timers world).(timerSignalSem) 0 perr (tmr_task_kernel world)
          eid observed tmr_task_legacy_any sg.(g_OSTmrSemSignal))
        (AppRep (tmr_task_application world)) heap).
Proof.
  intros Application AppRep environment critical sg call mask perr world eid observed
    Hprofile Hinit Hdomain Hentry heap
    [local [kernel [client [Hwhole [Hkernel
      [error [application [Hclient [Herror Happlication]]]]]]]]].
  destruct (TmrTaskFieldsRules.join_assoc application error kernel client heap
    (TmrTaskFieldsRules.join_comm _ _ _ Hclient)
    (TmrTaskFieldsRules.join_comm _ _ _ Hwhole)) as [owned [Hparts Hjoin]].
  assert (Hraw : TmrTaskFieldsRules.lift
    (UCOS2_C_Rules.sepcon
      (TmrTaskFields.tmr_task_fields_context environment local sg call mask (tmr_task_kernel world))
      (sem_pend_error_cell perr)) owned).
  { apply (proj2 (TmrTaskFieldsRules.lift_sepcon _ _ owned)).
    exists kernel, error; split.
    - apply TmrTaskFieldsRules.join_comm; exact Hparts.
    - split; assumption. }
  pose proof (TmrTaskClientPendHeap.context_split_pend_argument environment local critical sg call
    mask perr (tmr_task_kernel world) eid observed (tmr_task_client_pend_profile_enabled sg Hprofile)
    Hinit Hdomain Hentry (fst owned) Hraw) as Hargument.
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ owned) Hargument)
    as [cell [rest [Hargumentjoin [Hcell Hrest]]]].
  exists local, owned, application; split.
  - apply TmrTaskFieldsRules.join_comm; exact Hjoin.
  - split; [|exact Happlication]. exists cell, rest; split; [exact Hargumentjoin|]. split.
    + exact (proj2 (tmr_task_fields_cell_lift TaskPointerCell sg.(g_OSTmrSemSignal)
        (tmr_task_timers world).(timerSignalSem)) cell Hcell).
    + intros supplied combined Hcombined Hsupplied.
      apply (proj1 (TmrTaskFieldsRules.lift_wand _ _ rest) Hrest supplied combined Hcombined).
      exact (proj1 (tmr_task_fields_cell_lift TaskPointerCell sg.(g_OSTmrSemSignal)
        (tmr_task_timers world).(timerSignalSem)) supplied Hsupplied).
Qed.

Lemma tmr_task_client_pend_source : forall Application environment critical sg callback
  call signal (before : tmr_task_scan_world Application) error returned current,
  sem_pend_client_runtime_program environment critical sg call signal 0 (fst before) error current ->
  kernel_stack_call_same_call returned call ->
  tmr_task_client_pend_program environment critical sg (tmr_task_framed_effects callback)
    call signal before (error, returned) (current, snd before).
Proof. intros; split; [assumption|]. split; [assumption|reflexivity]. Qed.

(** The Sem pure carrier owns a real separated heap. Keep it as the
    residual while rebuilding the actual returned local and application
    frame. No carrier is discarded or converted to emp. *)
Lemma tmr_task_client_pend_post_world : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr) environment critical sg callback
  call mask perr signal (before : tmr_task_scan_world Application) X,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (tmr_task_client_pend_lifted_post environment critical sg call mask signal 0 perr (fst before) X)
      (AppRep (snd before)))
    (fun heap => exists returned current local error,
      tmr_task_client_pend_program environment critical sg (tmr_task_framed_effects callback)
        call signal before (error, returned) (current, snd before) /\
      tmr_task_client_pend_entry sg returned current /\
      safeExec (LastSeen current) (StateRelMonad.ret error) X /\
      TmrTaskFieldsRules.sepcon tmr_task_call_residual
        (tmr_task_fields_owned AppRep environment sg mask perr local returned (current, snd before)) heap).
Proof.
  intros Application AppRep environment critical sg callback call mask perr signal before X heap
    [owned [application [Hjoin [Hpost Happlication]]]].
  destruct Hpost as [returned [current [local [error Hpost]]]].
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ owned) Hpost)
    as [carrier [resources [Hsplit [Hfacts Hresources]]]].
  destruct (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ resources) Hresources)
    as [error_heap [kernel [Hparts [Herror Hkernel]]]].
  destruct Hfacts as [Hprogram [Hreturn [Hsame Hentry]]].
  destruct (TmrTaskFieldsRules.join_assoc carrier resources application owned heap Hsplit Hjoin)
    as [rest [Hrest Hwhole]].
  destruct (TmrTaskFieldsRules.join_assoc kernel error_heap application resources rest
    (TmrTaskFieldsRules.join_comm _ _ _ Hparts) Hrest)
    as [client [Hclient Howner]].
  exists returned, current, local, error; split.
  - apply tmr_task_client_pend_source; assumption.
  - split; [exact Hentry|]. split; [exact Hreturn|].
    exists carrier, rest; split; [exact Hwhole|]. split; [exact I|].
    exists kernel, client; split; [exact Howner|]. split; [exact Hkernel|].
    exists error_heap, application; split; [exact Hclient|]. split; [|exact Happlication].
    assert (Hweaken : UCOS2_C_Rules.derivable1
      (UCOS2_C_Rules.store_uchar perr error) (sem_pend_error_cell perr)).
    { unfold sem_pend_error_cell; apply UCOS2_C_Rules.store_uchar_undef_store_uchar. }
    exact (Hweaken (fst error_heap) Herror).
Qed.
