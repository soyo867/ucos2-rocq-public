(** Additive TimerPhase output for the current OS_InitTaskIdle source.
    Entry domain, actual callee posts, errors, resources and arbitrary X are unchanged. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.core.spec.init_task_idle_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_init_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

Lemma init_task_idle_name_post_phase :
  forall critical sg invocation name before error current X,
  task_name_set_post critical sg invocation 63 name before error current
    (init_task_idle_name_continuation X) ->
  before.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase).
Proof.
  intros; symmetry; eapply tmr_init_name_set_post_phase_frame; exact H.
Qed.

Lemma init_task_idle_post_name_phase : forall environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial X,
  init_task_idle_post environment critical saved_local sg entry base task_return
    lower old_frame upper original mask LitMap literals initial X |--
  EX returned middle create_error current name_error,
    coq_prop (safeExec (eq current) (StateRelMonad.ret tt) X /\
      middle.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase)) &&
    (coq_prop (init_task_idle_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned middle create_error) **
     coq_prop (task_name_set_post critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle")
        middle name_error current (init_task_idle_name_continuation X)) **
     task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask current **
     init_task_idle_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned middle create_error ** GlobalStrings_missing LitMap literals).
Proof.
  intros; unfold init_task_idle_post; Intros returned middle create_error current name_error.
  assert (Hname : task_name_set_post critical sg returned.(os_sched_call_invocation) 63
    (LitMap "uC/OS-II Idle") middle name_error current (init_task_idle_name_continuation X)) by tauto.
  pose proof (init_task_idle_name_post_phase _ _ _ _ _ _ _ _ Hname).
  Exists returned middle create_error current name_error; entailer!; tauto.
Qed.

Lemma init_task_idle_create_phase_post_open :
  forall environment critical saved_local sg entry base task_return
    lower old_frame upper original mask LitMap literals initial X error,
  initial.(SchedState).(isRunning) = false ->
  task_create_ext_boot_phase_post environment critical saved_local sg (init_task_idle_stack_region base)
    (init_task_idle_create_args entry base) task_return lower old_frame upper [] (lower ++ old_frame ++ upper) []
    original mask initial error
    (init_task_idle_create_postcondition environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X) ** GlobalStrings_missing LitMap literals |--
  EX returned middle,
    coq_prop (init_task_idle_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned middle error /\
      initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase) /\
      task_name_set_admission critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle") middle /\
      task_name_set_safe critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle") middle
        (init_task_idle_name_continuation X)) &&
    (task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask middle **
     init_task_idle_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned middle error ** GlobalStrings_missing LitMap literals).
Proof.
  intros; unfold task_create_ext_boot_phase_post; Intros returned middle.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hsafe : task_create_safe middle (StateRelMonad.ret error)
    (init_task_idle_create_postcondition environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X)) by tauto.
  destruct Hsafe as [start [Hstart Hsafe]]; subst start.
  specialize (Hsafe error middle (conj eq_refl eq_refl)).
  assert (Hcodes : error = 0 \/ error = 40 \/ error = 60 \/ error = 66).
  { assert (Hex : error = 42 -> 63 < (init_task_idle_create_args entry base).(createPriority)) by tauto.
    cbn in Hex; tauto || lia. }
  assert (Hinvocation : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation))
    by (unfold task_tcb_init_stack_same_call in Hsame; tauto).
  assert (Hadmit : task_name_set_admission critical sg returned.(os_sched_call_invocation) 63
    (LitMap "uC/OS-II Idle") middle).
  { eapply init_task_idle_name_admission; exact (proj1 (proj2 (proj2 Hsafe))). }
  assert (Hname : task_name_set_safe critical sg returned.(os_sched_call_invocation) 63
    (LitMap "uC/OS-II Idle") middle (init_task_idle_name_continuation X)).
  { rewrite Hinvocation; exact (proj2 (proj2 (proj2 Hsafe))). }
  sep_apply_l_atomic (proj1 (init_task_idle_name_call_resource_equiv environment critical saved_local sg returned mask middle)); Intros.
  Exists returned middle; unfold init_task_idle_created, init_task_idle_create_residual,
    init_task_idle_after_lower, init_task_idle_after_upper; entailer!; tauto.
Qed.

Lemma init_task_idle_create_name_phase_consequence :
  forall environment critical saved_local sg entry base task_return
    lower old_frame upper original mask LitMap literals initial X error,
  initial.(SchedState).(isRunning) = false ->
  task_create_ext_boot_phase_post environment critical saved_local sg (init_task_idle_stack_region base)
    (init_task_idle_create_args entry base) task_return lower old_frame upper [] (lower ++ old_frame ++ upper) []
    original mask initial error
    (init_task_idle_create_postcondition environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X) ** GlobalStrings_missing LitMap literals |--
  EX returned middle,
    coq_prop (init_task_idle_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned middle error /\
      task_name_set_admission critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle") middle /\
      task_name_set_safe critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle") middle
        (init_task_idle_name_continuation X) /\
      forall name_error current,
        task_name_set_post critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle")
          middle name_error current (init_task_idle_name_continuation X) ->
        initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase) /\
        middle.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase) /\
        safeExec (eq current) (StateRelMonad.ret tt) X) &&
    (task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask middle **
     init_task_idle_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned middle error ** GlobalStrings_missing LitMap literals).
Proof.
  intros environment critical saved_local sg entry base task_return lower old_frame upper
    original mask LitMap literals initial X error Hstop.
  sep_apply_l_atomic (init_task_idle_create_phase_post_open environment critical saved_local sg entry base task_return
    lower old_frame upper original mask LitMap literals initial X error Hstop); Intros returned middle.
  assert (Hchain : forall name_error current,
    task_name_set_post critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle")
      middle name_error current (init_task_idle_name_continuation X) ->
    initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase) /\
    middle.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase) /\
    safeExec (eq current) (StateRelMonad.ret tt) X).
  { intros name_error current Hname; split; [tauto|]. split.
    - eapply init_task_idle_name_post_phase; exact Hname.
    - eapply init_task_idle_name_post_safe_return; exact Hname. }
  Exists returned middle; entailer!; tauto.
Qed.

Definition init_task_idle_boot_phase_post environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned middle create_error current name_error,
    coq_prop (safeExec (eq current) (StateRelMonad.ret tt) X /\
      initial.(TimerState).(timerInitPhase) = middle.(TimerState).(timerInitPhase) /\
      middle.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase)) &&
    (coq_prop (init_task_idle_created environment critical sg entry base task_return lower old_frame upper
      original mask LitMap initial X returned middle create_error) **
     coq_prop (task_name_set_post critical sg returned.(os_sched_call_invocation) 63 (LitMap "uC/OS-II Idle")
        middle name_error current (init_task_idle_name_continuation X)) **
     task_name_set_closed environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) mask current **
     init_task_idle_create_residual environment saved_local sg entry base task_return lower old_frame upper
       returned middle create_error ** GlobalStrings_missing LitMap literals).

Lemma init_task_idle_boot_phase_post_forget : forall environment critical saved_local sg entry base task_return
  lower old_frame upper original mask LitMap literals initial X,
  init_task_idle_boot_phase_post environment critical saved_local sg entry base task_return
    lower old_frame upper original mask LitMap literals initial X |--
  init_task_idle_post environment critical saved_local sg entry base task_return
    lower old_frame upper original mask LitMap literals initial X.
Proof.
  intros; unfold init_task_idle_boot_phase_post; Intros returned middle create_error current name_error.
  unfold init_task_idle_post; Exists returned middle create_error current name_error; entailer!; tauto.
Qed.
