Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.

Module TmrTaskFields.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The Scheduler returns an actual local family and the CURRENT parked
    map. Timer accesses retain that family, rather than equating it with
    an earlier task-create family. Supplemental Flag padding is an outer
    frame and is never silently relabelled as current padding. *)
Definition tmr_task_fields_context environment local sg call mask state : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state.

Definition tmr_task_fields_timer_frame environment local sg call mask state : Assertion :=
  kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) call mask **
  (coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
   (UCOS2_fields_raw_rep_missing_module sg state TimerModule **
    unmap_table_rep sg **
    store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
        state.(TskState) local) state.(TskState).(parkedTaskStacks))).

Lemma tmr_task_fields_context_split_timer : forall environment local sg call mask state,
  tmr_task_fields_context environment local sg call mask state --||--
  coq_prop (UCOS2_state_inv sg state) &&
    (timer_configured_rep sg state.(TimerState) **
     tmr_task_fields_timer_frame environment local sg call mask state).
Proof.
  intros; unfold tmr_task_fields_context, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_program_fields_inv, kernel_program_fields_rep.
  rewrite (UCOS2_fields_raw_rep_split_module sg state TimerModule) by discriminate.
  cbn [UCOS2_module_rep].
  unfold tmr_task_fields_timer_frame; split; entailer!.
Qed.

Lemma tmr_task_fields_timer_frame_replace : forall environment local sg call mask state timers,
  tmr_task_fields_timer_frame environment local sg call mask state =
  tmr_task_fields_timer_frame environment local sg call mask (replace_TimerS timers state).
Proof. intros; reflexivity. Qed.

Lemma tmr_task_fields_context_merge_timer : forall environment local sg call mask state timers,
  UCOS2_state_inv sg (replace_TimerS timers state) ->
  timer_configured_rep sg timers **
    tmr_task_fields_timer_frame environment local sg call mask state |--
  tmr_task_fields_context environment local sg call mask (replace_TimerS timers state).
Proof.
  intros environment local sg call mask state timers Hvalid.
  rewrite (tmr_task_fields_timer_frame_replace environment local sg call mask state timers).
  rewrite (tmr_task_fields_context_split_timer environment local sg call mask
    (replace_TimerS timers state)); cbn [replace_TimerS]; entailer!.
Qed.

Lemma tmr_task_fields_context_valid : forall environment local sg call mask state,
  tmr_task_fields_context environment local sg call mask state |--
  coq_prop (UCOS2_state_inv sg state) &&
    tmr_task_fields_context environment local sg call mask state.
Proof.
  intros; rewrite tmr_task_fields_context_split_timer; entailer!.
Qed.

(** This consumes the actual same-state native world. It splits existing
    bytes; it does not produce a world for a future state. *)
Lemma tmr_task_fields_context_from_native : forall environment critical saved_local sg call mask state,
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
    unmap_table_rep sg |--
  tmr_task_fields_context environment (task_create_continuation_local saved_local)
    sg call mask state ** flag_configured_padding_rep sg state.(FlagState).
Proof.
  intros; apply (proj1 (os_sched_unlock_native_fields_padding
    environment critical saved_local sg call mask state)).
Qed.

(** Both actual Unlock alternatives feed the same Task resource shape.
    The scheduled branch keeps next_local and the original padding map;
    the native branch uses its own returned state. No equality between
    old and current task maps or local families is a premise. *)
Lemma tmr_task_fields_context_from_unlock_return : forall environment critical saved_local
  sg returned mask current,
  os_sched_unlock_continuation_return_world environment critical saved_local
    sg returned mask current |--
  EX local padding,
    tmr_task_fields_context environment local sg returned mask current **
      flag_configured_padding_rep sg padding.
Proof.
  intros environment critical saved_local sg returned mask current heap Hworld.
  destruct Hworld as [Hnative | [reference [entry [local [Hfacts Hscheduled]]]]].
  - exists (task_create_continuation_local saved_local), current.(FlagState).
    exact (tmr_task_fields_context_from_native environment critical saved_local
      sg returned mask current heap Hnative).
  - exists local, entry.(FlagState); exact Hscheduled.
Qed.

End TmrTaskFields.

Module TmrTaskFieldsRules := TimerCallback_C_Rules.Rules.

Section TaskFieldsOwner.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

(** The error byte and application resources remain outside the kernel
    callee's footprint. The existential hides ONLY the actual local family;
    the returned kernel state and call context stay explicit. *)
Definition tmr_task_fields_owned local call
  (world : (UCOS2_Verify_State * Application)%type) : TmrTaskFieldsRules.expr :=
  TmrTaskFieldsRules.sepcon
    (TmrTaskFieldsRules.lift
      (TmrTaskFields.tmr_task_fields_context environment local sg call mask (fst world)))
    (TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.lift (sem_pend_error_cell perr))
      (AppRep (snd world))).

Definition tmr_task_current_fields_owned call
  (world : (UCOS2_Verify_State * Application)%type) : TmrTaskFieldsRules.expr :=
  fun heap => exists local, tmr_task_fields_owned local call world heap.

Lemma tmr_task_current_fields_owned_intro : forall local call world,
  TmrTaskFieldsRules.derivable1 (tmr_task_fields_owned local call world)
    (tmr_task_current_fields_owned call world).
Proof. intros local call world heap Howned; exists local; exact Howned. Qed.

Lemma tmr_task_current_fields_owned_valid : forall call world,
  TmrTaskFieldsRules.derivable1 (tmr_task_current_fields_owned call world)
    (TmrTaskFieldsRules.andp
      (TmrTaskFieldsRules.coq_prop (UCOS2_state_inv sg (fst world)))
      (tmr_task_current_fields_owned call world)).
Proof.
  intros call world heap Howned; split; [|exact Howned].
  destruct Howned as [local [kernel [rest [Hjoin [Hkernel Hrest]]]]].
  exact (proj1 (TmrTaskFields.tmr_task_fields_context_valid environment local
    sg call mask (fst world) (fst kernel) Hkernel)).
Qed.

End TaskFieldsOwner.
