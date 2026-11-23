Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_callback_contract_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.ucos2_verify_inv.
Require Import Coq.ZArith.ZArith.

Module TmrTaskCallOld.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** The pure separating conjunct in the canonical SemPend post may own
    an arbitrary residual.  Keep that exact residual as TT instead of
    dropping it when exposing the current returned resources. *)
Definition pend_return_resources external platform environment critical saved_local
  sg context returned mask perr final error : Assertion :=
  TT ** (perr # UChar |-> error **
    sem_post_return_resources external platform critical sg context returned mask final **
    sem_pend_optional_continuation_resources external platform (Some environment)
      saved_local returned final).

Lemma pend_post_open : forall external platform environment critical saved_local sg
  context mask signal perr before X,
  sem_pend_continuation_call_post external platform (Some environment) critical
    saved_local sg context mask signal 0 perr before X |--
  EX final, EX returned, EX error,
    coq_prop (sem_pend_runtime_program external platform (Some environment) critical sg
      context signal 0 before error final /\ kernel_stack_call_same_call returned context) &&
    pend_return_resources external platform environment critical saved_local sg context
      returned mask perr final error.
Proof.
  intros external platform environment critical saved_local sg context mask signal perr
    before X heap [final [returned [error [pure_heap [resources [Hjoin
      [[Hsource [Hlegacy Hsame]] Hresources]]]]]]].
  exists final, returned, error; split; [exact (conj Hsource Hsame)|].
  exists pure_heap, resources; split; [exact Hjoin|]. split; [exact I|exact Hresources].
Qed.

Lemma context_lock_pre : forall platform critical sg invocation origin mask before,
  mutex_query_closed platform critical sg invocation origin mask before |--
  os_sched_lock_program_pre platform critical sg invocation origin mask before (fun _ => True).
Proof.
  intros platform critical sg invocation origin mask before heap Hclosed; split.
  - exists before; split; [reflexivity|].
    unfold safe, StateRelHoare.weakestpre; hnf; intros; exact I.
  - exact (proj2 (os_sched_lock_pre_closed_equiv platform critical sg invocation origin
      mask before) heap Hclosed).
Qed.

Lemma context_unlock_pre : forall external platform critical sg context mask before,
  os_sched_unlock_acquire_safety external critical sg context before ->
  mutex_query_closed platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask before **
  (os_sched_context_resources external context ** unmap_table_rep sg) |--
  os_sched_unlock_program_pre external platform critical sg context mask before (fun _ => True).
Proof.
  intros external platform critical sg context mask before Hready.
  assert (Hbase :
    mutex_query_closed platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask before **
    (os_sched_context_resources external context ** unmap_table_rep sg) |--
    coq_prop (UCOS2_state_inv sg before /\
      os_sched_unlock_acquire_safety external critical sg context before) &&
    os_sched_unlock_outside_frame external platform critical sg context mask before).
  { intros heap [closed [caller [Hjoin [[Hvalid Hclosed] Hcaller]]]].
    split; [exact (conj Hvalid Hready)|].
    unfold os_sched_unlock_outside_frame.
    apply (UCOS2_C_Rules.derivable1_sepcon_assoc1 _ _ _ heap).
    exists closed, caller; split; [exact Hjoin|]. split; assumption. }
  intros heap Hcontext; split.
  - exists before; split; [reflexivity|].
    unfold safe, StateRelHoare.weakestpre; hnf; intros; exact I.
  - apply (proj2 (os_sched_unlock_pre_closed_equiv external platform critical sg
      context mask before) heap); exact (Hbase heap Hcontext).
Qed.
End TmrTaskCallOld.

Section TaskCallResources.
Context {Application : Type} (AppRep : Application -> TmrTaskRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  (mask perr : Z).

Definition tmr_task_call_locals (context : OsSchedCallContext)
  (kernel : UCOS2_Verify_State) (application : Application) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon (TmrTaskRules.lift (sem_pend_error_cell perr))
    (TmrTaskRules.sepcon
      (TmrTaskRules.lift (sem_pend_optional_continuation_resources external platform
        (Some environment) saved_local context kernel)) (AppRep application)).

Lemma tmr_task_call_locals_task_state_eq : forall context before after application,
  before.(TskState) = after.(TskState) ->
  tmr_task_call_locals context before application =
    tmr_task_call_locals context after application.
Proof.
  intros context before after application Htask.
  unfold tmr_task_call_locals, sem_pend_optional_continuation_resources,
    task_tcb_init_continuation_capsules; rewrite Htask; reflexivity.
Qed.

Lemma tmr_task_call_locals_timer_update : forall context before timers application,
  tmr_task_call_locals context before application =
    tmr_task_call_locals context (replace_TimerS timers before) application.
Proof. intros; apply tmr_task_call_locals_task_state_eq; reflexivity. Qed.

Lemma tmr_task_call_locals_same_call : forall context returned kernel application,
  kernel_stack_call_same_call returned context ->
  tmr_task_call_locals context kernel application =
    tmr_task_call_locals returned kernel application.
Proof.
  intros context returned kernel application Hsame.
  unfold tmr_task_call_locals.
  rewrite (sem_pend_optional_continuation_same_call external platform (Some environment)
    saved_local returned context kernel Hsame); reflexivity.
Qed.

Definition tmr_task_call_pend_post (context : OsSchedCallContext) signal
  (before : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon
    (TmrTaskRules.lift (sem_pend_continuation_call_post external platform (Some environment)
      critical saved_local sg context mask signal 0 perr (fst before) (fun _ _ => True)))
    (AppRep (snd before)).

Lemma tmr_task_call_pend_post_continue : forall Result context signal before
  (next : (Z * OsSchedCallContext) ->
    StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  safeExec (eq before)
    (StateRelMonad.bind (tmr_task_pend_program external platform environment critical sg
      (tmr_task_framed_effects callback) context signal) next) X ->
  TmrTaskRules.derivable1 (tmr_task_call_pend_post context signal before)
    (fun heap => exists kernel returned error,
      sem_pend_runtime_program external platform (Some environment) critical sg context
        signal 0 (fst before) error kernel /\
      kernel_stack_call_same_call returned context /\
      safeExec (eq (kernel, snd before)) (next (error, returned)) X /\
      TmrTaskRules.sepcon
        (TmrTaskRules.lift (TmrTaskCallOld.pend_return_resources external platform environment
          critical saved_local sg context returned mask perr kernel error))
        (AppRep (snd before)) heap).
Proof.
  intros Result context signal before next X Hsafe heap
    [callee [application [Hjoin [Hpost Happ]]]].
  destruct (TmrTaskCallOld.pend_post_open external platform environment critical saved_local
    sg context mask signal perr (fst before) (fun _ _ => True) (fst callee) Hpost)
    as [kernel [returned [error [[Hsource Hsame] Hresources]]]].
  exists kernel, returned, error; split; [exact Hsource|]. split; [exact Hsame|]. split.
  - eapply tmr_task_stage_continue; [|exact Hsafe].
    split; [exact Hsource|]. split; [exact Hsame|reflexivity].
  - exists callee, application; split; [exact Hjoin|]. split; assumption.
Qed.

Definition tmr_task_call_lock_pre (context : OsSchedCallContext)
  (before : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon
    (TmrTaskRules.sepcon
      (TimerCalleeLift.os_sched_lock_program_pre platform critical sg
        context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
        (fst before) (fun _ => True))
      (TmrTaskRules.sepcon (TimerCalleeLift.os_sched_context_resources external context)
        (TimerCalleeLift.unmap_table_rep sg)))
    (tmr_task_call_locals context (fst before) (snd before)).

Definition tmr_task_call_lock_post (context : OsSchedCallContext)
  (before : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon
    (TmrTaskRules.sepcon
      (TimerCalleeLift.os_sched_lock_program_post platform critical sg
        context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
        (fst before) (fun _ => True))
      (TmrTaskRules.sepcon (TimerCalleeLift.os_sched_context_resources external context)
        (TimerCalleeLift.unmap_table_rep sg)))
    (tmr_task_call_locals context (fst before) (snd before)).

Lemma tmr_task_call_lock_pre_open : forall context before,
  TmrTaskRules.derivable1
    (tmr_task_owned AppRep external platform environment critical saved_local sg
      mask perr context before)
    (tmr_task_call_lock_pre context before).
Proof.
  intros context before heap
    [context_heap [locals [Hwhole
      [[closed [caller [Hcontext [Hclosed Hcaller]]]] Hlocals]]]].
  exists context_heap, locals; split; [exact Hwhole|]. split; [|exact Hlocals].
  exists closed, caller; split; [exact Hcontext|]. split; [|exact Hcaller].
  exact (TmrTaskCallOld.context_lock_pre platform critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
    (fst before) (fst closed) Hclosed).
Qed.

Lemma tmr_task_call_lock_post_continue : forall Result context before
  (next : unit -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  safeExec (eq before)
    (StateRelMonad.bind (tmr_task_lock_program critical sg
      (tmr_task_framed_effects callback) context) next) X ->
  TmrTaskRules.derivable1 (tmr_task_call_lock_post context before)
    (fun heap => exists entry kernel,
      os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
        (fst before) entry kernel /\
      safeExec (eq (kernel, snd before)) (next tt) X /\
      TmrTaskRules.sepcon
        (tmr_task_context_rep external platform critical sg mask context kernel)
        (tmr_task_call_locals context (fst before) (snd before)) heap).
Proof.
  intros Result context before next X Hsafe heap
    [context_heap [locals [Hwhole
      [[callee [caller [Hcontext [Hpost Hcaller]]]] Hlocals]]]].
  destruct (TimerCalleeLift.os_sched_lock_program_post_closed_return platform critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
    (fst before) (fun _ => True) callee Hpost)
    as [entry [kernel [[Hsource Htrue] Hclosed]]].
  exists entry, kernel; split; [exact Hsource|]. split.
  - eapply tmr_task_stage_continue; [|exact Hsafe].
    split; [split; [reflexivity|exists entry; exact Hsource]|reflexivity].
  - exists context_heap, locals; split; [exact Hwhole|]. split; [|exact Hlocals].
    exists callee, caller; split; [exact Hcontext|]. split; assumption.
Qed.

(** This opening consumes the actual acquire-safety premise of the current
    Unlock C contract.  It is not manufactured from Timer validity. *)
Definition tmr_task_call_unlock_pre (context : OsSchedCallContext)
  (before : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon
    (TimerCalleeLift.os_sched_unlock_program_pre external platform critical sg context
      mask (fst before) (fun _ => True))
    (tmr_task_call_locals context (fst before) (snd before)).

Definition tmr_task_call_unlock_post (context : OsSchedCallContext)
  (before : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.sepcon
    (TimerCalleeLift.os_sched_unlock_program_post external platform critical sg context
      mask (fst before) (fun _ => True))
    (tmr_task_call_locals context (fst before) (snd before)).

Lemma tmr_task_call_unlock_pre_open : forall context before,
  os_sched_unlock_acquire_safety external critical sg context (fst before) ->
  TmrTaskRules.derivable1
    (tmr_task_owned AppRep external platform environment critical saved_local sg
      mask perr context before)
    (tmr_task_call_unlock_pre context before).
Proof.
  intros context before Hready heap [context_heap [locals [Hjoin [Hcontext Hlocals]]]].
  exists context_heap, locals; split; [exact Hjoin|]. split; [|exact Hlocals].
  pose proof (proj1 (TimerCalleeLift.os_sched_closed_resources_lift external platform
    critical sg context mask (fst before)) context_heap Hcontext) as Hold.
  exact (TmrTaskCallOld.context_unlock_pre external platform critical sg context mask
    (fst before) Hready (fst context_heap) Hold).
Qed.

Lemma tmr_task_call_unlock_post_continue : forall Result context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  os_sched_unlock_acquire_safety external critical sg context (fst before) ->
  safeExec (eq before)
    (StateRelMonad.bind (tmr_task_unlock_program external critical sg
      (tmr_task_framed_effects callback) context) next) X ->
  TmrTaskRules.derivable1 (tmr_task_call_unlock_post context before)
    (fun heap => exists returned kernel,
      os_sched_unlock_call_relation external critical sg context (fst before) returned kernel /\
      kernel_stack_call_same_call returned context /\
      safeExec (eq (kernel, snd before)) (next returned) X /\
      TmrTaskRules.sepcon
        (tmr_task_context_rep external platform critical sg mask returned kernel)
        (tmr_task_call_locals context (fst before) (snd before)) heap).
Proof.
  intros Result context before next X Hready Hsafe heap
    [callee [locals [Hjoin [Hpost Hlocals]]]].
  destruct (TimerCalleeLift.os_sched_unlock_program_post_closed_return external platform
    critical sg context mask (fst before) (fun _ => True) Hready callee Hpost)
    as [returned [kernel [[Hsource Htrue] Hcontext]]].
  exists returned, kernel; split; [exact Hsource|]. split.
  - exact (TimerCalleeLift.os_sched_unlock_call_relation_context_fields external critical sg
      context (fst before) returned kernel Hsource).
  - split.
    + eapply tmr_task_stage_continue; [|exact Hsafe]. split; [exact Hsource|reflexivity].
    + exists callee, locals; split; [exact Hjoin|]. split; assumption.
Qed.

Lemma tmr_task_call_return_reindex : forall context returned before after application,
  kernel_stack_call_same_call returned context -> before.(TskState) = after.(TskState) ->
  TmrTaskRules.derivable1
    (TmrTaskRules.sepcon
      (tmr_task_context_rep external platform critical sg mask returned after)
      (tmr_task_call_locals context before application))
    (tmr_task_owned AppRep external platform environment critical saved_local sg
      mask perr returned (after, application)).
Proof.
  intros context returned before after application Hsame Htask.
  rewrite (tmr_task_call_locals_same_call context returned before application Hsame).
  rewrite (tmr_task_call_locals_task_state_eq returned before after application Htask).
  intros heap Howned; exact Howned.
Qed.
End TaskCallResources.
