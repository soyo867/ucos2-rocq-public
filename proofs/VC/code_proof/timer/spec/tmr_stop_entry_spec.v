Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_fields_spec.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

(** Entry cutpoints for the unchanged OSTmrStop carrier.  Until its first
    actual output store, error is a ghost with no represented byte value.
    AppRep owns the remaining application resources, disjoint from perr.
    An argument equal to perr denotes this one cell, not a second resource.

    These lemmas transport actual callee postconditions.  Their source
    proofs, acquisition preconditions, typed field/store rules and callback
    capabilities must still be supplied at the C call sites.  safeExec
    supplies only the same-X continuation, never execution capability. *)
Section StopEntry.
Context {Application : Type}.
Context (AppRep : Application -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (effects : TmrStopEffects Application) (mask perr : Z).

Definition tmr_stop_entry_client_rep (current : TmrStopState Application)
  : TmrStopRules.expr :=
  TmrStopRules.sepcon (TmrStopRules.undef_store_uchar perr)
    (AppRep current.(tmr_stop_application)).

Definition tmr_stop_entry_owned (context : OsSchedCallContext)
  (current : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (tmr_stop_context_rep external platform critical sg mask context current.(tmr_stop_kernel))
    (tmr_stop_entry_client_rep current).

Lemma tmr_stop_entry_owned_set_error : forall context error (before : TmrStopState Application),
  tmr_stop_entry_owned context (tmr_stop_set_error error before) =
  tmr_stop_entry_owned context before.
Proof. reflexivity. Qed.

(** The premise below is the POST of the real typed store.  There is no
    entailment from undef_store_uchar to an initialized output byte. *)
Lemma tmr_stop_first_store_continue : forall (Result : Type) context error
  (before : TmrStopState Application)
  (next : unit -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop),
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_store_error_program error) next) X ->
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (tmr_stop_context_rep external platform critical sg mask context before.(tmr_stop_kernel))
      (TmrStopRules.sepcon (TmrStopRules.store_uchar perr error)
        (AppRep before.(tmr_stop_application))))
    (TmrStopRules.andp
      (TmrStopRules.coq_prop
        (safeExec (eq (tmr_stop_set_error error before)) (next tt) X))
      (tmr_stop_owned AppRep external platform critical sg mask perr context
        (tmr_stop_set_error error before))).
Proof.
  intros Result context error before next X Hsafe heap Hstore; split; [|exact Hstore].
  eapply tmr_stop_stage_continue; [|exact Hsafe]. split; reflexivity.
Qed.

(** The explicit application premise must come from the actual private
    frame protocol.  In particular it must hold for whichever error ghost
    is used at entry; it is not inferred from the high-level safeExec. *)
Lemma tmr_stop_entry_lock_frame : forall (Result : Type) context
  (before : TmrStopState Application)
  (next : unit -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop),
  (forall entry kernel,
    os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
      before.(tmr_stop_kernel) entry kernel ->
    tmr_stop_lock_application effects context before (tmr_stop_set_kernel kernel before)) ->
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_lock_program critical sg effects context) next) X ->
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (TmrStopRules.sepcon
        (TimerCalleeLift.os_sched_lock_program_post platform critical sg
          context.(os_sched_call_invocation) context.(os_sched_call_origin) mask
          before.(tmr_stop_kernel) (fun _ => True))
        (TmrStopRules.sepcon
          (TimerCalleeLift.os_sched_context_resources external context)
          (TimerCalleeLift.unmap_table_rep sg)))
      (tmr_stop_entry_client_rep before))
    (fun heap => exists after,
      tmr_stop_lock_program critical sg effects context before tt after /\
      safeExec (eq after) (next tt) X /\ tmr_stop_entry_owned context after heap).
Proof.
  intros Result context before next X Happ Hsafe heap
    [context_heap [client_heap [Houter
      [[kernel_heap [stack_heap [Hinner [Hpost Hstack]]]] Hclient]]]].
  destruct (TimerCalleeLift.os_sched_lock_program_post_closed_return
    platform critical sg context.(os_sched_call_invocation) context.(os_sched_call_origin)
    mask before.(tmr_stop_kernel) (fun _ => True) kernel_heap Hpost)
    as [entry [kernel [[Hcall Htrue] Hclosed]]].
  assert (Hstep : tmr_stop_lock_program critical sg effects context before tt
    (tmr_stop_set_kernel kernel before)).
  { split.
    - split; [reflexivity|exists entry; exact Hcall].
    - apply (Happ entry kernel); exact Hcall. }
  exists (tmr_stop_set_kernel kernel before); split; [exact Hstep|].
  split; [eapply tmr_stop_stage_continue; eassumption|].
  exists context_heap, client_heap; split; [exact Houter|]. split; [|exact Hclient].
  exists kernel_heap, stack_heap; split; [exact Hinner|split; assumption].
Qed.

(** Non-running paths use this rule BEFORE their first output store.
    The acquired scheduler state and returned context are those of the
    actual Unlock relation; final validity needs its independent safety. *)
Lemma tmr_stop_entry_unlock_frame : forall (Result : Type) context
  (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop),
  os_sched_unlock_acquire_safety external critical sg context before.(tmr_stop_kernel) ->
  (forall returned kernel,
    os_sched_unlock_call_relation external critical sg context
      before.(tmr_stop_kernel) returned kernel ->
    tmr_stop_unlock_application effects context before returned (tmr_stop_set_kernel kernel before)) ->
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_unlock_program external critical sg effects context) next) X ->
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (TimerCalleeLift.os_sched_unlock_program_post external platform critical sg
        context mask before.(tmr_stop_kernel) (fun _ => True))
      (tmr_stop_entry_client_rep before))
    (fun heap => exists returned after,
      tmr_stop_unlock_program external critical sg effects context before returned after /\
      safeExec (eq after) (next returned) X /\ tmr_stop_entry_owned returned after heap).
Proof.
  intros Result context before next X Hready Happ Hsafe heap
    [kernel_heap [client_heap [Hjoin [Hpost Hclient]]]].
  destruct (TimerCalleeLift.os_sched_unlock_program_post_closed_return
    external platform critical sg context mask before.(tmr_stop_kernel) (fun _ => True)
    Hready kernel_heap Hpost) as [returned [kernel [[Hcall Htrue] Hcontext]]].
  assert (Hstep : tmr_stop_unlock_program external critical sg effects context before returned
    (tmr_stop_set_kernel kernel before)).
  { split; [exact Hcall|apply (Happ returned kernel); exact Hcall]. }
  exists returned, (tmr_stop_set_kernel kernel before); split; [exact Hstep|].
  split; [eapply tmr_stop_stage_continue; eassumption|].
  exists kernel_heap, client_heap; split; [exact Hjoin|split; assumption].
Qed.

Lemma tmr_stop_entry_unlink_frame : forall (Result : Type) context
  (before : TmrStopState Application) index node
  (next : unit -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop),
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized before.(tmr_stop_kernel).(TimerState) ->
  before.(tmr_stop_kernel).(TimerState).(timerUsed) index = Some node ->
  node.(timerState) = TimerRunning ->
  safeExec (eq before) (StateRelMonad.bind (tmr_stop_unlink_program sg index) next) X ->
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (TmrStopRules.sepcon
        (TimerCalleeLift.tmr_unlink_configured_post sg before.(tmr_stop_kernel).(TimerState) index)
        (tmr_stop_unlink_frame external platform sg mask context before))
      (tmr_stop_entry_client_rep before))
    (fun heap => exists after,
      tmr_stop_unlink_program sg index before tt after /\
      safeExec (eq after) (next tt) X /\ tmr_stop_entry_owned context after heap).
Proof.
  intros Result context before index node next X Henabled Hinit Hnode Hrunning Hsafe heap
    [context_heap [client_heap [Hjoin [Hpost Hclient]]]].
  pose proof (proj2 (TmrStopRules.lift_sepcon _ _ context_heap) Hpost) as Hlifted.
  pose proof (TmrStopRules.lift_entailment _ _
    (TmrStopOldFields.unlink_post_merge_context external platform critical sg context mask
      before.(tmr_stop_kernel) index node Henabled Hinit Hnode Hrunning)
    context_heap Hlifted) as Hmerged.
  destruct Hmerged as [timers [Hstep Hcontext]].
  assert (Hcommand : tmr_stop_unlink_program sg index before tt
    (tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before)).
  { apply tmr_stop_unlink_step; exact Hstep. }
  exists (tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before).
  split; [exact Hcommand|]. split; [eapply tmr_stop_stage_continue; eassumption|].
  exists context_heap, client_heap; split; [exact Hjoin|]. split; [|exact Hclient].
  exact (proj2 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask (replace_TimerS timers before.(tmr_stop_kernel))) context_heap Hcontext).
Qed.
End StopEntry.

(** This is pure address/current-image binding, not ownership or a claim
    that an earlier image survives Lock.  The source pointer must equal
    timer_pool_addr with the real sg address symbols and configured size. *)
Definition tmr_stop_pooled_binding (sg : StableGlobVars) (pointer index : Z)
  (current : GlobTimerState) : Prop :=
  pointer = timer_pool_addr sg index /\ pointer <> 0 /\
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers) /\
  timer_api_initialized current /\ exists image, current.(timerImages) index = Some image.

Lemma tmr_stop_pooled_binding_has_image : forall sg pointer index current,
  tmr_stop_pooled_binding sg pointer index current ->
  exists image, pointer = timer_pool_addr sg index /\ current.(timerImages) index = Some image.
Proof.
  intros sg pointer index current [Hpointer [_ [_ [_ [image Himage]]]]].
  exists image; split; assumption.
Qed.

Lemma tmr_stop_pooled_binding_storage_frame : forall sg pointer index before after,
  timer_public_storage_frame before after ->
  tmr_stop_pooled_binding sg pointer index before ->
  tmr_stop_pooled_binding sg pointer index after.
Proof.
  intros sg pointer index before after Hframe [Hpointer [Hnonnull [Hrange [Hinit Himage]]]].
  split; [exact Hpointer|]. split; [exact Hnonnull|]. split; [exact Hrange|]. split.
  - eapply timer_public_storage_frame_initialized; eassumption.
  - destruct Himage as [image Himage].
    eapply timer_public_storage_frame_has_image; eassumption.
Qed.

(** The final AppRep must supply the typed cells witnessing these views.
    These equalities only establish independence from the output ghost;
    they do not assert any raw field value or turn raw State=3 into Unlink
    ownership.  Raw State=1/2/error paths remain in the source program. *)
Definition tmr_stop_raw_getter {Application : Type} (view : Application -> Z)
  (current : TmrStopState Application) : Z := view current.(tmr_stop_application).

Lemma tmr_stop_raw_getter_set_error : forall (Application : Type)
  (view : Application -> Z) error (before : TmrStopState Application),
  tmr_stop_raw_getter view (tmr_stop_set_error error before) = tmr_stop_raw_getter view before.
Proof. reflexivity. Qed.

Lemma tmr_stop_raw_getter_set_kernel : forall (Application : Type)
  (view : Application -> Z) kernel (before : TmrStopState Application),
  tmr_stop_raw_getter view (tmr_stop_set_kernel kernel before) = tmr_stop_raw_getter view before.
Proof. reflexivity. Qed.
