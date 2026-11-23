(** Ordered CreateExt/NameSet composition for the unchanged OS_InitTaskStat body.
    The real CreateExt returned context is consumed by NameSet. The output
    owns only the actual named/current continuation world; the private child
    failure buffer and missing literal pool remain separate. *)
Require Export Ucos2Verify.VC.code.core.spec.init_task_stat_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_task_idle_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_ext_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_name_set_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.


Lemma init_task_stat_continuation_name_api_pre_entry :
  forall environment critical saved_local sg region args task_return lower old_frame upper
    call mask initial LitMap literals,
  task_create_name_api_pre environment critical saved_local sg region args task_return
    lower old_frame upper call mask initial LitMap literals |--
  coq_prop (task_create_stack_entry sg args (LitMap "?") call initial) &&
  task_create_name_api_pre environment critical saved_local sg region args task_return
    lower old_frame upper call mask initial LitMap literals.
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    call mask initial LitMap literals heap Hpre.
  split; [|exact Hpre].
  pose proof (task_create_name_api_pre_open environment critical saved_local sg region args task_return
    lower old_frame upper call mask initial LitMap literals heap Hpre) as [_ Hopened].
  destruct Hopened as (owned & strings & Hjoin & Hcontinuation & Hstrings).
  exact (proj1 (proj1 Hcontinuation)).
Qed.

Definition init_task_stat_continuation_phase_frame (before after : UCOS2_Verify_State) : Prop :=
  before.(TimerState).(timerInitPhase) = after.(TimerState).(timerInitPhase).

Definition init_task_stat_continuation_create_program environment critical sg entry base task_return
  lower old_frame upper call mask LitMap :=
  task_create_ext_continuation_program environment critical sg (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return
    (init_task_stat_after_lower entry base lower old_frame upper)
    (init_task_stat_after_upper entry base lower old_frame upper) (LitMap "?") call mask.

Definition init_task_stat_continuation_sequence environment critical sg entry base task_return
  lower old_frame upper call mask LitMap : program UCOS2_Verify_State OsSchedCallContext :=
  StateRelMonad.bind
    (init_task_stat_continuation_create_program environment critical sg entry base task_return
      lower old_frame upper call mask LitMap)
    (fun created => StateRelMonad.bind
      (task_name_set_continuation_call_program environment critical sg (fst created) mask 62 (LitMap "uC/OS-II Stat"))
      (fun named => StateRelMonad.ret (fst named))).

Definition init_task_stat_continuation_safe environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (init_task_stat_continuation_sequence environment critical sg entry base task_return
      lower old_frame upper call mask LitMap) X.

Definition init_task_stat_continuation_name_postcondition
  (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop)
  : OsSchedCallContext -> Z -> UCOS2_Verify_State -> Prop := fun returned _ current => X returned current.

Definition init_task_stat_continuation_create_postcondition environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop)
  : OsSchedCallContext -> Z -> UCOS2_Verify_State -> Prop := fun returned error current =>
  init_task_stat_continuation_create_program environment critical sg entry base task_return
    lower old_frame upper call mask LitMap before (returned, error) current /\
  init_task_stat_boot_frame before current /\
  readable_name current.(NameState) (LitMap "uC/OS-II Stat") init_task_stat_name_chars /\
  task_create_stack_entry sg (init_task_stat_create_args entry base) (LitMap "?") returned current /\
  task_name_set_continuation_call_safe environment critical sg returned mask 62 (LitMap "uC/OS-II Stat") current
    (init_task_stat_continuation_name_postcondition X).

Lemma init_task_stat_continuation_safe_create : forall environment critical sg entry base task_return
  lower old_frame upper call mask LitMap before X,
  before.(SchedState).(isRunning) = false ->
  task_create_stack_entry sg (init_task_stat_create_args entry base) (LitMap "?") call before ->
  readable_name before.(NameState) (LitMap "uC/OS-II Stat") init_task_stat_name_chars ->
  init_task_stat_continuation_safe environment critical sg entry base task_return
    lower old_frame upper call mask LitMap before X ->
  task_create_ext_continuation_safe before
    (init_task_stat_continuation_create_program environment critical sg entry base task_return
      lower old_frame upper call mask LitMap)
    (init_task_stat_continuation_create_postcondition environment critical sg entry base task_return
      lower old_frame upper call mask LitMap before X).
Proof.
  intros environment critical sg entry base task_return lower old_frame upper call mask LitMap before X Hstop Hentry Hread Hsafe.
  destruct Hsafe as [start [Hstart Hsafe]]; subst start.
  exists before; split; [reflexivity|].
  intros [returned error] current Hcreate; cbn.
  assert (Herased : init_task_stat_create_program environment critical sg entry base task_return
    lower old_frame upper call mask LitMap before error current).
  { eapply (task_create_ext_continuation_program_error_projection environment critical sg
      (init_task_stat_stack_region base) (init_task_stat_create_args entry base) task_return
      (init_task_stat_after_lower entry base lower old_frame upper)
      (init_task_stat_after_upper entry base lower old_frame upper) (LitMap "?") call mask
      before returned error current); exact Hcreate. }
  pose proof (init_task_stat_create_preserves_boot environment critical sg (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return
    (init_task_stat_after_lower entry base lower old_frame upper)
    (init_task_stat_after_upper entry base lower old_frame upper) (LitMap "?") call mask
    before error current Hstop Herased) as Hframe.
  split; [exact Hcreate|]. split; [exact Hframe|]. split.
  - rewrite <- (proj2 Hframe); exact Hread.
  - split.
    + eapply init_task_continuation_program_preserves_entry; [exact Hstop|cbn; lia|exact Hentry|exact Hcreate].
    + exists current; split; [reflexivity|]. intros [named name_error] final Hname; cbn.
    apply (Hsafe named final).
    exists (returned, error), current; split; [exact Hcreate|].
    exists (named, name_error), final; split; [exact Hname|split; reflexivity].
Qed.

Definition init_task_stat_continuation_failure_buffer entry base task_return lower old_frame upper error : Assertion :=
  if Z.eq_dec error 0 then emp else
    task_stack_storage (init_task_stat_stack_region base)
      (if Z.eq_dec error 66 then task_create_stack_image TaskStackNoVFP
        (init_task_stat_create_args entry base) task_return
        (init_task_stat_after_lower entry base lower old_frame upper)
        (init_task_stat_after_upper entry base lower old_frame upper)
       else lower ++ old_frame ++ upper).

Definition init_task_stat_continuation_created environment critical sg entry base task_return lower old_frame upper
  original mask LitMap initial X returned middle error : Prop :=
  task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg middle /\
  (error = 0 \/ error = 40 \/ error = 60 \/ error = 66) /\
  init_task_stat_continuation_create_postcondition environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial X returned error middle.

Lemma init_task_stat_continuation_create_post_open : forall environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial X error,
  initial.(SchedState).(isRunning) = false ->
  task_create_ext_continuation_boot_phase_post environment critical saved_local sg (init_task_stat_stack_region base)
    (init_task_stat_create_args entry base) task_return lower old_frame upper [] (lower ++ old_frame ++ upper) []
    original mask initial error
    (init_task_stat_continuation_create_postcondition environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X) ** GlobalStrings_missing LitMap literals |--
  EX returned middle,
    coq_prop (init_task_stat_continuation_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned middle error /\
      initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase) /\
      task_name_set_continuation_admission sg returned 62 (LitMap "uC/OS-II Stat") middle /\
      task_name_set_continuation_call_safe environment critical sg returned mask 62 (LitMap "uC/OS-II Stat") middle
        (init_task_stat_continuation_name_postcondition X)) &&
    (task_name_set_continuation_closed environment critical saved_local sg returned mask middle **
     init_task_stat_continuation_failure_buffer entry base task_return lower old_frame upper error **
     GlobalStrings_missing LitMap literals).
Proof.
  intros; unfold task_create_ext_continuation_boot_phase_post; Intros returned middle.
  assert (Hsafe : task_create_ext_continuation_safe middle (StateRelMonad.ret (returned, error))
    (init_task_stat_continuation_create_postcondition environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X)) by tauto.
  destruct Hsafe as [start [Hstart Hsafe]]; subst start.
  specialize (Hsafe (returned, error) middle (conj eq_refl eq_refl)).
  change (init_task_stat_continuation_create_postcondition environment critical sg entry base task_return
    lower old_frame upper original mask LitMap initial X returned error middle) in Hsafe.
  assert (Hname : task_name_set_continuation_call_safe environment critical sg returned mask 62
    (LitMap "uC/OS-II Stat") middle (init_task_stat_continuation_name_postcondition X)).
  { exact (proj2 (proj2 (proj2 (proj2 Hsafe)))). }
  assert (Hcodes : error = 0 \/ error = 40 \/ error = 60 \/ error = 66).
  { assert (Hex : error = 42 -> 63 < (init_task_stat_create_args entry base).(createPriority)) by tauto.
    cbn in Hex; tauto || lia. }
  assert (Hadmit : task_name_set_continuation_admission sg returned 62 (LitMap "uC/OS-II Stat") middle).
  { eapply task_name_set_continuation_admission_explicit; [lia|exact (proj1 (proj2 (proj2 Hsafe)))]. }
  Exists returned middle; unfold init_task_stat_continuation_created, init_task_stat_continuation_failure_buffer,
    task_name_set_continuation_closed, init_task_stat_after_lower, init_task_stat_after_upper; entailer!; tauto.
Qed.

Definition init_task_stat_continuation_literal_residual environment critical saved_local sg call mask state name : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
  (init_task_stat_name_call_residual environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) mask state name **
   task_name_set_continuation_resources environment saved_local sg call state).

Lemma init_task_stat_continuation_split_literal : forall environment critical saved_local sg call mask state name,
  readable_name state.(NameState) name init_task_stat_name_chars ->
  task_name_set_continuation_closed environment critical saved_local sg call mask state |--
  store_stringLit name "uC/OS-II Stat" **
  init_task_stat_continuation_literal_residual environment critical saved_local sg call mask state name.
Proof.
  intros * Hread; rewrite task_name_set_continuation_closed_split; Intros.
  sep_apply_l_atomic (init_task_stat_name_call_split_literal environment.(task_stack_call_platform)
    critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin) mask state name Hread).
  unfold init_task_stat_continuation_literal_residual; entailer!.
Qed.

Lemma init_task_stat_continuation_merge_literal : forall environment critical saved_local sg call mask state name,
  store_stringLit name "uC/OS-II Stat" **
  init_task_stat_continuation_literal_residual environment critical saved_local sg call mask state name |--
  task_name_set_continuation_closed environment critical saved_local sg call mask state.
Proof.
  intros; unfold init_task_stat_continuation_literal_residual; Intros.
  sep_apply_l_atomic (init_task_stat_name_call_merge_literal environment.(task_stack_call_platform)
    critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin) mask state name).
  rewrite task_name_set_continuation_closed_split; entailer!.
Qed.

Lemma init_task_stat_continuation_source_names :
  forall environment critical sg observer event_observer first before stopped last after,
  kernel_resumption_task_source_trace environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg observer event_observer first before stopped last after ->
  before.(NameState) = after.(NameState).
Proof.
  intros * Htrace.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace) as [Hresource _].
  eapply kernel_client_resource_trace_preserves_name_state.
  - intros; eapply critical_region_client_name_frame; eassumption.
  - eapply kernel_resumption_resource_trace_erases; exact Hresource.
Qed.

Lemma init_task_stat_continuation_save_history_names :
  forall environment critical sg original before returned acquired,
  kernel_call_save_history environment critical sg original before returned acquired ->
  before.(NameState) = acquired.(NameState).
Proof.
  intros * Hhistory; destruct Hhistory; try reflexivity;
    match goal with
    | Htrace : kernel_resumption_task_source_trace _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (init_task_stat_continuation_source_names _ _ _ _ _ _ _ _ _ _ Htrace) as Hnames
    end;
    match type of Hnames with
    | NameState (armv7a_irq_live_parked_state ?initial ?call ?sp ?fragments) = _ =>
      assert (Hframe : NameState (armv7a_irq_live_parked_state initial call sp fragments) = NameState initial)
        by (unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp;
            change (NameState (armv7a_irq_entry_counter_state initial) = NameState initial);
            unfold armv7a_irq_entry_counter_state;
            destruct (isRunning (SchedState initial)); reflexivity);
      rewrite Hframe in Hnames; exact Hnames
    end.
Qed.

Lemma init_task_stat_continuation_restore_history_names :
  forall environment critical sg original before returned current,
  kernel_call_restore_history environment critical sg original before returned current ->
  before.(NameState) = current.(NameState).
Proof.
  intros * Hhistory; destruct Hhistory; try reflexivity;
    match goal with
    | Htrace : kernel_resumption_task_source_trace _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (init_task_stat_continuation_source_names _ _ _ _ _ _ _ _ _ _ Htrace) as Hnames
    end;
    match type of Hnames with
    | NameState (armv7a_irq_live_parked_state ?initial ?call ?sp ?fragments) = _ =>
      assert (Hframe : NameState (armv7a_irq_live_parked_state initial call sp fragments) = NameState initial)
        by (unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp;
            change (NameState (armv7a_irq_entry_counter_state initial) = NameState initial);
            unfold armv7a_irq_entry_counter_state;
            destruct (isRunning (SchedState initial)); reflexivity);
      rewrite Hframe in Hnames; exact Hnames
    end.
Qed.

Lemma init_task_stat_continuation_save_effect_names :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired ->
  before.(NameState) = acquired.(NameState).
Proof.
  intros * [[Htrace _]|[Hhistory _]].
  - eapply init_task_stat_continuation_source_names; exact Htrace.
  - eapply init_task_stat_continuation_save_history_names; exact Hhistory.
Qed.

Lemma init_task_stat_continuation_restore_effect_names :
  forall environment critical sg original released returned current,
  os_sched_continuation_restore_effect environment critical sg original released returned current ->
  released.(NameState) = current.(NameState).
Proof.
  intros * [[Htrace _]|Hhistory].
  - eapply init_task_stat_continuation_source_names; exact Htrace.
  - eapply init_task_stat_continuation_restore_history_names; exact Hhistory.
Qed.

Lemma init_task_stat_continuation_name_result_names :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_result environment critical sg original mask request name before returned error current ->
  before.(NameState) = current.(NameState).
Proof.
  intros * Hresult; unfold task_name_set_continuation_result in Hresult.
  destruct Hresult as [Hbad|[Hnull|[Hisr|Hresult]]].
  - destruct Hbad as (_ & _ & -> & _); reflexivity.
  - destruct Hnull as (_ & _ & _ & -> & _); reflexivity.
  - destruct Hisr as (_ & _ & _ & _ & -> & _); reflexivity.
  - destruct Hresult as (_ & _ & _ & saved & active & acquired & priority & released & Hsave & _ & Hstep & Hrestore).
    pose proof (init_task_stat_continuation_save_effect_names _ _ _ _ _ _ _ _ _ Hsave) as Hfirst.
    pose proof (init_task_stat_continuation_restore_effect_names _ _ _ _ _ _ _ Hrestore) as Hlast.
    inversion Hstep; subst;
      unfold task_name_set_update in Hlast; cbn [NameState replace_TskS] in Hlast;
      (etransitivity; [exact Hfirst|exact Hlast]).
Qed.

Lemma init_task_stat_continuation_name_post_safe_return :
  forall environment critical sg original mask request name before named error current X,
  task_name_set_continuation_call_post environment critical sg original mask request name before named error current
    (init_task_stat_continuation_name_postcondition X) ->
  safeExec (eq current) (StateRelMonad.ret named) X.
Proof.
  intros * [_ [_ [start [Hstart Hsafe]]]]; subst start.
  exists current; split; [reflexivity|].
  intros returned final [Hreturned Hfinal]; subst returned final.
  exact (Hsafe (named, error) current (conj eq_refl eq_refl)).
Qed.

Lemma init_task_stat_continuation_uninitialized_stopped : forall sg state,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg state ->
  state.(TimerState).(timerInitPhase) = TimerUninitialized -> state.(SchedState).(isRunning) = false.
Proof.
  intros sg state Henabled Hvalid Hphase.
  assert (Hcontrol : timer_running_initialization_consistency sg state)
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency in Hvalid; tauto).
  unfold timer_running_initialization_consistency in Hcontrol.
  destruct (state.(SchedState).(isRunning)) eqn:Hrunning; [|reflexivity].
  specialize (Hcontrol Henabled eq_refl); congruence.
Qed.

Definition init_task_stat_continuation_post environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial (X : OsSchedCallContext -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned middle create_error named current name_error,
    coq_prop (safeExec (eq current) (StateRelMonad.ret named) X /\
      task_create_stack_entry sg (init_task_stat_create_args entry base) (LitMap "?") named current /\
      task_tcb_init_stack_same_call named original /\
      initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase) /\
      middle.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase) /\
      initial.(NameState) = current.(NameState) /\
      (sg.(osKernelConfig).(cfgTimerEnabled) = true ->
       initial.(TimerState).(timerInitPhase) = TimerUninitialized -> current.(SchedState).(isRunning) = false) /\
      init_task_stat_continuation_created environment critical sg entry base task_return lower old_frame upper
        original mask LitMap initial X returned middle create_error /\
      task_name_set_continuation_call_post environment critical sg returned mask 62 (LitMap "uC/OS-II Stat")
        middle named name_error current (init_task_stat_continuation_name_postcondition X)) &&
    (coq_prop (init_task_stat_continuation_created environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial X returned middle create_error) **
  coq_prop (task_name_set_continuation_call_post environment critical sg returned mask 62 (LitMap "uC/OS-II Stat")
    middle named name_error current (init_task_stat_continuation_name_postcondition X)) **
  coq_prop (init_task_stat_continuation_phase_frame initial middle) **
  task_name_set_continuation_closed environment critical saved_local sg named mask current **
     init_task_stat_continuation_failure_buffer entry base task_return lower old_frame upper create_error **
     GlobalStrings_missing LitMap literals).

Lemma init_task_stat_continuation_post_close : forall environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial X returned middle create_error named current name_error,
  init_task_stat_continuation_created environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial X returned middle create_error ->
  initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase) ->
  task_name_set_continuation_call_post environment critical sg returned mask 62 (LitMap "uC/OS-II Stat")
    middle named name_error current (init_task_stat_continuation_name_postcondition X) ->
  coq_prop (init_task_stat_continuation_created environment critical sg entry base task_return lower old_frame upper
    original mask LitMap initial X returned middle create_error) **
  coq_prop (task_name_set_continuation_call_post environment critical sg returned mask 62 (LitMap "uC/OS-II Stat")
    middle named name_error current (init_task_stat_continuation_name_postcondition X)) **
  coq_prop (init_task_stat_continuation_phase_frame initial middle) **
  task_name_set_continuation_closed environment critical saved_local sg named mask current **
  init_task_stat_continuation_failure_buffer entry base task_return lower old_frame upper create_error **
  GlobalStrings_missing LitMap literals |--
  init_task_stat_continuation_post environment critical saved_local sg entry base task_return lower old_frame upper
    original mask LitMap literals initial X.
Proof.
  intros * Hcreated Hphase Hname.
  pose proof (task_name_set_continuation_call_result_phase _ _ _ _ _ _ _ _ _ _ _ (proj1 Hname)) as Hlast.
  pose proof (init_task_stat_continuation_name_result_names _ _ _ _ _ _ _ _ _ _ _
    (task_name_set_continuation_call_result_forget _ _ _ _ _ _ _ _ _ _ _ (proj1 Hname))) as Hnames.
  pose proof (init_task_stat_continuation_name_post_safe_return environment critical sg returned mask 62
    (LitMap "uC/OS-II Stat") middle named name_error current X Hname) as Hsafe.
  assert (Hfirst_names : initial.(NameState) = middle.(NameState)).
  { unfold init_task_stat_continuation_created, init_task_stat_continuation_create_postcondition,
      init_task_stat_boot_frame in Hcreated; tauto. }
  assert (Hmiddle_entry : task_create_stack_entry sg (init_task_stat_create_args entry base) (LitMap "?") returned middle).
  { unfold init_task_stat_continuation_created, init_task_stat_continuation_create_postcondition in Hcreated; tauto. }
  pose proof (init_task_continuation_name_post_preserves_entry environment critical sg
    (init_task_stat_create_args entry base) (LitMap "?") returned mask 62
    (LitMap "uC/OS-II Stat") middle named name_error current
    (init_task_stat_continuation_name_postcondition X) Hmiddle_entry Hname) as Hcurrent_entry.
  assert (Hsame : task_tcb_init_stack_same_call named original).
  { pose proof (proj1 Hcreated) as Hfirst_same.
    pose proof (task_name_set_continuation_call_result_same_call _ _ _ _ _ _ _ _ _ _ _ (proj1 Hname)) as Hlast_same.
    unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  unfold task_name_set_continuation_closed, task_create_continuation_input; Intros.
  assert (Hboot : sg.(osKernelConfig).(cfgTimerEnabled) = true ->
    initial.(TimerState).(timerInitPhase) = TimerUninitialized -> current.(SchedState).(isRunning) = false).
  { intros; eapply init_task_stat_continuation_uninitialized_stopped; [eassumption|tauto|congruence]. }
  unfold init_task_stat_continuation_post; Exists returned middle create_error named current name_error.
  unfold task_name_set_continuation_closed, task_create_continuation_input; entailer!; intuition congruence.
Qed.
