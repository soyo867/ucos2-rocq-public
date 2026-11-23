Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_api_program_spec.
Require Export Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.
Require Export Ucos2Verify.VC.code.timer.spec.timer_callee_lift_spec.
Require Import Coq.ZArith.ZArith.
From MonadLib.MonadErr Require Import MonadErrBasic.

Import Monad MonadNotation.
Local Open Scope Z_scope.

Module TmrStopCallback := TimerCallback_C_Rules.
Module TmrStopRules := TimerCallback_C_Rules.Rules.

(** Use explicit StateRelMonad names below.  MonadErrBasic also exports a
    [program] notation; import order must not select the high-level monad.
    The actual callback command remains the distinct MonadErr semantics. *)

(** Spatial cutpoints for the unchanged OSTmrStop source carrier.

    Source binding is still a proof obligation: the fixed carrier must be
    rebuilt with the original headers/configuration; field reads and stores
    must use its actual addresses; Lock, Unlock and Unlink must discharge
    their current C obligations.  TimerCalleeLift transports assertions and
    proved entailments, not a source Hoare theorem for those callees.

    The callback rule below is stronger than projecting a selected abstract
    transition.  It consumes the actual indirect-call rule, including its
    coverage of EVERY normal outcome of the registered source body.  The
    only capability introduction requires that body's source evidence and
    the actual address/body lookup.  No effects record alone creates a C
    capability or a resource transition.

    The byte at perr occurs once in owned.  AppRep owns the remaining client
    resources.  In particular callback_arg = perr is allowed and refers to
    this same byte; there is no separately framed argument cell.  As in the
    source-program candidate, the output cell is disjoint from the kernel
    representation.  Kernel-field/output overlap is not a claimed domain.

    pre and post are the program/representation interfaces.  Supplying pre
    does not by itself discharge a callback capability, a raw field read or
    callee acquisition safety: those are explicit call-site obligations in
    the rules below and in the canonical C annotation still to be checked. *)

Section StopSpatial.

Context {Application : Type}.
Context (AppRep : Application -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (effects : TmrStopEffects Application) (mask perr : Z).

Definition tmr_stop_context_rep (context : OsSchedCallContext)
  (kernel : UCOS2_Verify_State) : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TimerCalleeLift.mutex_query_closed platform critical sg
      context.(os_sched_call_invocation) context.(os_sched_call_origin) mask kernel)
    (TmrStopRules.sepcon
      (TimerCalleeLift.os_sched_context_resources external context)
      (TimerCalleeLift.unmap_table_rep sg)).

Definition tmr_stop_client_rep (current : TmrStopState Application)
  : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TmrStopRules.store_uchar perr current.(tmr_stop_error))
    (AppRep current.(tmr_stop_application)).

Definition tmr_stop_owned (context : OsSchedCallContext)
  (current : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon (tmr_stop_context_rep context current.(tmr_stop_kernel))
    (tmr_stop_client_rep current).

Definition tmr_stop_unlock_ready (context : OsSchedCallContext)
  (current : TmrStopState Application) : Prop :=
  os_sched_unlock_acquire_safety external critical sg context current.(tmr_stop_kernel).

Lemma tmr_stop_output_cell_unique : forall first second,
  TmrStopRules.derivable1
    (TmrStopRules.sepcon (TmrStopRules.store_uchar perr first)
      (TmrStopRules.store_uchar perr second))
    (TmrStopRules.coq_prop False).
Proof.
  intros first second heap [left_heap [right_heap [Hjoin [Hleft Hright]]]].
  destruct Hleft as [Hleft_range Hleft].
  destruct Hright as [Hright_range Hright].
  apply (TmrStopRules.dup_mstore_noninit perr heap).
  exists left_heap, right_heap; split; [exact Hjoin|].
  split; eapply TmrStopRules.mstore_mstore_noninit; eassumption.
Qed.

(** The callback may change the timer's state, delete/recreate its slot,
    update arbitrary owned application cells, and write the output byte.
    Its normal return must provide the CURRENT resources and the ordinary
    acquisition safety needed by the next, real OSSchedUnlock call. *)
Definition tmr_stop_callback_pre (self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (arguments : (Z * Z)%type) : TmrStopRules.expr :=
  TmrStopRules.andp (TmrStopRules.coq_prop (arguments = (self, argument)))
    (tmr_stop_owned context before).

Definition tmr_stop_callback_post (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (arguments : (Z * Z)%type) (_ : unit) : TmrStopRules.expr :=
  fun heap => exists returned after,
    arguments = (self, argument) /\
    tmr_stop_callback effects fn self argument context before returned after /\
    tmr_stop_unlock_ready returned after /\
    tmr_stop_owned returned after heap.

Definition tmr_stop_callback_capability (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  : TmrStopRules.expr :=
  TmrStopCallback.func_ptr_spec fn
    (TmrStopCallback.HoareFun TmrStopCallback.timer_callback_signature
      (tmr_stop_callback_pre self argument context before)
      (tmr_stop_callback_post fn self argument context before)).

Definition tmr_stop_callback_call_pre (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (frame : TmrStopRules.expr) : TmrStopRules.expr :=
  @TmrStopCallback.call_pre TmrStopCallback.timer_callback_signature fn (self, argument)
    (tmr_stop_callback_pre self argument context before)
    (tmr_stop_callback_post fn self argument context before) frame.

Lemma tmr_stop_callback_pre_open : forall fn self argument context before frame,
  TmrStopRules.derivable1
    (TmrStopRules.andp
      (TmrStopRules.sepcon (tmr_stop_owned context before) frame)
      (tmr_stop_callback_capability fn self argument context before))
    (tmr_stop_callback_call_pre fn self argument context before frame).
Proof.
  intros fn self argument context before frame heap
    [[owned_heap [frame_heap [Hjoin [Howned Hframe]]]] Hcap].
  split; [|exact Hcap].
  exists owned_heap, frame_heap; split; [exact Hjoin|].
  split; [split; [reflexivity|exact Howned]|exact Hframe].
Qed.

Lemma tmr_stop_callback_capability_from_source : forall fn self argument context before
  (environment : TmrStopCallback.callback_environment)
  (body : TmrStopCallback.FunSem TmrStopCallback.timer_callback_signature),
  fn <> 0 ->
  TmrStopCallback.source_functions environment TmrStopCallback.timer_callback_signature fn = Some body ->
  TmrStopCallback.callback_source_evidence environment TmrStopCallback.timer_callback_signature body
    (tmr_stop_callback_pre self argument context before)
    (tmr_stop_callback_post fn self argument context before) ->
  forall heap,
    tmr_stop_callback_capability fn self argument context before (heap, environment).
Proof.
  intros fn self argument context before environment body Hfn Hlookup Hevidence heap.
  eapply TmrStopCallback.func_ptr_hoare_from_source_evidence; eassumption.
Qed.

Definition tmr_stop_callback_resume {Result : Type} (fn self argument : Z)
  (context : OsSchedCallContext) (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) (frame : TmrStopRules.expr)
  : TmrStopRules.expr :=
  fun heap => exists returned after,
    tmr_stop_callback effects fn self argument context before returned after /\
    tmr_stop_unlock_ready returned after /\
    safeExec (eq after) (next returned) X /\
    TmrStopRules.sepcon (tmr_stop_owned returned after) frame heap /\
    tmr_stop_callback_capability fn self argument context before heap.

Lemma tmr_stop_callback_post_continue : forall (Result : Type)
  fn self argument context (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) frame,
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_callback effects fn self argument context) next) X ->
  TmrStopRules.derivable1
    (@TmrStopCallback.call_post TmrStopCallback.timer_callback_signature fn (self, argument)
      (tmr_stop_callback_pre self argument context before)
      (tmr_stop_callback_post fn self argument context before) frame tt)
    (tmr_stop_callback_resume fn self argument context before next X frame).
Proof.
  intros Result fn self argument context before next X frame Hsafe heap
    [[owned_heap [frame_heap [Hjoin [Hpost Hframe]]]] Hcap].
  destruct Hpost as [returned [after [Hargs [Hstep [Hready Howned]]]]].
  exists returned, after; split; [exact Hstep|].
  split; [exact Hready|]. split.
  - eapply tmr_stop_stage_continue; eassumption.
  - split; [|exact Hcap].
    exists owned_heap, frame_heap; split; [exact Hjoin|split; assumption].
Qed.

(** Both conjuncts of indirect_call_rule are used: the first excludes an
    actual source fault, and the second supplies a resource interpretation
    for every actual source final memory.  The continuation is the SAME X
    supplied at the call cutpoint, with no callback-specific replacement. *)
Theorem tmr_stop_callback_source_rule : forall (Result : Type)
  fn self argument context (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) frame initial,
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_callback effects fn self argument context) next) X ->
  tmr_stop_callback_call_pre fn self argument context before frame initial ->
  ~ @TmrStopCallback.source_call_error TmrStopCallback.timer_callback_signature
      (snd initial) fn (self, argument)
      (fst initial).(ConAssertion.s_mem) /\
  (forall final_memory,
    @TmrStopCallback.source_call_normal TmrStopCallback.timer_callback_signature
      (snd initial) fn (self, argument)
      (fst initial).(ConAssertion.s_mem) tt final_memory ->
    exists final,
      MonadErr.nrm (@TmrStopCallback.indirect_call TmrStopCallback.timer_callback_signature
        fn (self, argument)) initial tt final /\
      (fst final).(ConAssertion.s_mem) = final_memory /\
      tmr_stop_callback_resume fn self argument context before next X frame final).
Proof.
  intros Result fn self argument context before next X frame initial Hsafe Hpre.
  destruct (@TmrStopCallback.indirect_call_rule TmrStopCallback.timer_callback_signature fn (self, argument)
    (tmr_stop_callback_pre self argument context before)
    (tmr_stop_callback_post fn self argument context before) frame)
    as [Hhoare Hcoverage].
  split.
  - intro Herror. exact (proj2 Hhoare initial Hpre Herror).
  - intros final_memory Hsource.
    destruct (Hcoverage initial tt final_memory Hpre Hsource)
      as [final [Hnormal [Hmemory Hpost]]].
    exists final; split; [exact Hnormal|]. split; [exact Hmemory|].
    eapply tmr_stop_callback_post_continue; eassumption.
Qed.

(** These cutpoint lemmas consume kernel relations from the actual callee
    postcondition AND a separately proved application/output relation.
    The latter must be established by the source/frame bridge; it is never
    inferred from a kernel-only postcondition. *)
Lemma tmr_stop_lock_post_continue : forall (Result : Type) context
  (before after : TmrStopState Application)
  (next : unit -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) heap,
  os_sched_lock_program critical sg context.(os_sched_call_invocation)
    before.(tmr_stop_kernel) tt after.(tmr_stop_kernel) ->
  tmr_stop_lock_application effects context before after ->
  tmr_stop_owned context after heap ->
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_lock_program critical sg effects context) next) X ->
  safeExec (eq after) (next tt) X /\ tmr_stop_owned context after heap.
Proof.
  intros Result context before after next X heap Hkernel Happlication Howned Hsafe.
  split; [|exact Howned]. eapply tmr_stop_stage_continue; [|exact Hsafe].
  split; assumption.
Qed.

Lemma tmr_stop_unlock_post_continue : forall (Result : Type) context returned
  (before after : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) heap,
  os_sched_unlock_call_relation external critical sg context
    before.(tmr_stop_kernel) returned after.(tmr_stop_kernel) ->
  tmr_stop_unlock_application effects context before returned after ->
  tmr_stop_owned returned after heap ->
  safeExec (eq before)
    (StateRelMonad.bind (tmr_stop_unlock_program external critical sg effects context) next) X ->
  safeExec (eq after) (next returned) X /\ tmr_stop_owned returned after heap.
Proof.
  intros Result context returned before after next X heap Hkernel Happlication Howned Hsafe.
  split; [|exact Howned]. eapply tmr_stop_stage_continue; [|exact Hsafe].
  split; assumption.
Qed.

Lemma tmr_stop_unlink_post_continue : forall (Result : Type) index context
  (before : TmrStopState Application) timers
  (next : unit -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop) heap,
  timer_unlink sg before.(tmr_stop_kernel).(TimerState) index = Some timers ->
  tmr_stop_owned context
    (tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before) heap ->
  safeExec (eq before) (StateRelMonad.bind (tmr_stop_unlink_program sg index) next) X ->
  safeExec (eq (tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before))
    (next tt) X /\
  tmr_stop_owned context
    (tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before) heap.
Proof.
  intros Result index context before timers next X heap Hunlink Howned Hsafe.
  split; [|exact Howned]. eapply tmr_stop_stage_continue; [|exact Hsafe].
  apply tmr_stop_unlink_step; exact Hunlink.
Qed.

(** A useful specialization when the current output and client resources
    are retained as the callee's disjoint frame.  This is not a universal
    law about effects: the application relation is supplied explicitly.
    The general post_continue rules above also admit changed client state
    when its actual source protocol provides that postcondition. *)
Lemma tmr_stop_lock_framed_post_continue : forall (Result : Type) context
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
      (tmr_stop_client_rep before))
    (fun heap => exists after,
      tmr_stop_lock_program critical sg effects context before tt after /\
      safeExec (eq after) (next tt) X /\ tmr_stop_owned context after heap).
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
  exists context_heap, client_heap; split; [exact Houter|].
  split; [|exact Hclient].
  exists kernel_heap, stack_heap; split; [exact Hinner|split; assumption].
Qed.

Lemma tmr_stop_unlock_framed_post_continue : forall (Result : Type) context
  (before : TmrStopState Application)
  (next : OsSchedCallContext -> StateRelMonad.M (TmrStopState Application) Result)
  (X : Result -> TmrStopState Application -> Prop),
  tmr_stop_unlock_ready context before ->
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
      (tmr_stop_client_rep before))
    (fun heap => exists returned after,
      tmr_stop_unlock_program external critical sg effects context before returned after /\
      safeExec (eq after) (next returned) X /\ tmr_stop_owned returned after heap).
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

Definition tmr_stop_unlock_tail (context : OsSchedCallContext)
  : StateRelMonad.M (TmrStopState Application) tmr_stop_output :=
  StateRelMonad.bind (tmr_stop_unlock_program external critical sg effects context)
    (fun returned => StateRelMonad.bind (tmr_stop_finish_program 1 returned)
      (fun result => StateRelMonad.ret (tmr_stop_return_output result))).

Lemma tmr_stop_unlock_tail_step : forall context returned (before after : TmrStopState Application),
  tmr_stop_unlock_program external critical sg effects context before returned after ->
  tmr_stop_unlock_tail context before (1, after.(tmr_stop_error)) after.
Proof.
  intros context returned before after Hunlock; unfold tmr_stop_unlock_tail.
  exists returned, after; split; [exact Hunlock|].
  exists {| tmr_stop_return_value := 1;
            tmr_stop_return_error := after.(tmr_stop_error);
            tmr_stop_return_context := returned |}, after.
  split; split; reflexivity.
Qed.

Lemma tmr_stop_unlock_tail_result : forall context
  (before after : TmrStopState Application) output,
  tmr_stop_unlock_tail context before output after ->
  exists returned,
    tmr_stop_unlock_program external critical sg effects context before returned after /\
    output = (1, after.(tmr_stop_error)).
Proof.
  intros context before after output
    [returned [unlocked [Hunlock [result [finished [Hfinish Houtput]]]]]].
  destruct Hfinish as [Hresult Hfinished]; subst result; subst finished.
  destruct Houtput as [Houtput Hafter]; subst output; subst after.
  exists returned; split; [exact Hunlock|reflexivity].
Qed.

Lemma tmr_stop_unlock_tail_safe_return : forall context returned
  (before after : TmrStopState Application)
  (X : tmr_stop_output -> TmrStopState Application -> Prop),
  safeExec (eq before) (tmr_stop_unlock_tail context) X ->
  tmr_stop_unlock_program external critical sg effects context before returned after ->
  safeExec (eq after) (StateRelMonad.ret (1, after.(tmr_stop_error))) X.
Proof.
  intros context returned before after X Hsafe Hunlock.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final [Hresult Hfinal]; subst result; subst final.
  apply (Hsafe (1, after.(tmr_stop_error)) after).
  eapply tmr_stop_unlock_tail_step; exact Hunlock.
Qed.

Section PublicBranches.

Context (pooled : bool) (pointer index opt argument : Z)
  (raw_type raw_state : TmrStopState Application -> Z).

Local Notation stop_source :=
  (@tmr_stop_source_program Application external critical sg effects pooled
    pointer index opt argument raw_type raw_state).
Local Notation stop_safe :=
  (@tmr_stop_api_pre Application external critical sg effects pooled
    pointer index opt argument raw_type raw_state).
Local Notation stop_result :=
  (@tmr_stop_call_result Application external critical sg effects pooled
    pointer index opt argument raw_type raw_state).
Local Notation stop_post :=
  (@tmr_stop_api_post Application external critical sg effects pooled
    pointer index opt argument raw_type raw_state).

Definition tmr_stop_pre (context : OsSchedCallContext) (before : TmrStopState Application)
  (X : tmr_stop_output -> TmrStopState Application -> Prop) : TmrStopRules.expr :=
  TmrStopRules.andp (TmrStopRules.coq_prop (stop_safe context before X))
    (tmr_stop_owned context before).

Definition tmr_stop_post (context : OsSchedCallContext) (before : TmrStopState Application)
  (retcode : Z) (X : tmr_stop_output -> TmrStopState Application -> Prop)
  : TmrStopRules.expr :=
  fun heap => exists returned after,
    stop_post context before returned (retcode, after.(tmr_stop_error)) after X /\
    tmr_stop_owned returned after heap.

(** The complete public-program continuation reaches the real callback
    cutpoint through its actual type/ISR/Lock/State/Unlink/select prefix.
    This supplies the premise of callback_source_rule; that rule does not
    introduce an unrelated continuation merely for the indirect call. *)
Lemma tmr_stop_running_callback_continue : forall context
  (before observed locked state_read stopped selected : TmrStopState Application) request X,
  pointer <> 0 -> tmr_stop_type_program pooled index raw_type before 100 observed ->
  os_sched_lock_ints observed.(tmr_stop_kernel) <= 0 ->
  tmr_stop_lock_program critical sg effects context observed tt locked ->
  tmr_stop_state_program pooled index raw_state locked 3 state_read ->
  tmr_stop_unlink_program sg index state_read tt stopped ->
  tmr_stop_select_callback_program pointer index opt argument
    (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped) request selected ->
  stop_safe context before X ->
  safeExec (eq selected)
    (StateRelMonad.bind (tmr_stop_optional_callback_program effects request context) tmr_stop_unlock_tail) X.
Proof.
  intros context before observed locked state_read stopped selected request X
    Hpointer Htype Hints Hlock Hstate Hunlink Hselect Hsafe.
  unfold tmr_stop_api_pre, safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists selected; split; [reflexivity|].
  intros output final [callback_returned [callback_after [Hcallback Htail]]].
  destruct (tmr_stop_unlock_tail_result callback_returned callback_after final output Htail)
    as [returned [Hunlock Houtput]]; subst output.
  apply (Hsafe (1, final.(tmr_stop_error)) final).
  eapply tmr_stop_call_result_program with (returned := returned).
  unfold tmr_stop_call_result.
  eapply tmr_stop_source_locked_return with (observed := observed) (locked := locked);
    [exact Hpointer|exact Htype|exact Hints|exact Hlock|].
  eapply tmr_stop_locked_running_step with (observed := state_read); [exact Hstate|].
  exact (@tmr_stop_running_step Application external critical sg effects pointer index opt argument
    context state_read stopped request selected callback_returned callback_after returned final
    Hunlink Hselect Hcallback Hunlock).
Qed.

Lemma tmr_stop_source_return_post : forall context (before after : TmrStopState Application)
  returned retcode X heap,
  stop_safe context before X ->
  stop_result context before returned (retcode, after.(tmr_stop_error)) after ->
  tmr_stop_owned returned after heap ->
  tmr_stop_post context before retcode X heap.
Proof.
  intros context before after returned retcode X heap Hsafe Hresult Howned.
  exists returned, after; split; [|exact Howned].
  eapply tmr_stop_call_safe_return; eassumption.
Qed.

Lemma tmr_stop_null_return_post : forall context (before : TmrStopState Application) X heap,
  pointer = 0 -> stop_safe context before X ->
  tmr_stop_owned context
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_INVALID) before) heap ->
  tmr_stop_post context before 0 X heap.
Proof.
  intros context before X heap Hpointer Hsafe Howned.
  eapply tmr_stop_source_return_post; [exact Hsafe| |exact Howned].
  unfold tmr_stop_call_result; cbn [tmr_stop_set_error tmr_stop_error].
  apply tmr_stop_source_null_return; exact Hpointer.
Qed.

Lemma tmr_stop_type_return_post : forall context (before observed : TmrStopState Application)
  ty X heap,
  pointer <> 0 -> ty <> 100 ->
  tmr_stop_type_program pooled index raw_type before ty observed ->
  stop_safe context before X ->
  tmr_stop_owned context
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_INVALID_TYPE) observed) heap ->
  tmr_stop_post context before 0 X heap.
Proof.
  intros context before observed ty X heap Hpointer Htype Hread Hsafe Howned.
  eapply tmr_stop_source_return_post; [exact Hsafe| |exact Howned].
  unfold tmr_stop_call_result; cbn [tmr_stop_set_error tmr_stop_error].
  eapply tmr_stop_source_type_return; eassumption.
Qed.

Lemma tmr_stop_isr_return_post : forall context (before observed : TmrStopState Application)
  X heap,
  pointer <> 0 -> tmr_stop_type_program pooled index raw_type before 100 observed ->
  os_sched_lock_ints observed.(tmr_stop_kernel) > 0 -> stop_safe context before X ->
  tmr_stop_owned context
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_ISR) observed) heap ->
  tmr_stop_post context before 0 X heap.
Proof.
  intros context before observed X heap Hpointer Hread Hints Hsafe Howned.
  eapply tmr_stop_source_return_post; [exact Hsafe| |exact Howned].
  unfold tmr_stop_call_result; cbn [tmr_stop_set_error tmr_stop_error].
  eapply tmr_stop_source_isr_return; eassumption.
Qed.

(** This one branch rule covers STOPPED, COMPLETED, UNUSED and invalid
    State values.  There is no Start-style exclusion of raw State 1 or 2.
    The output store is after the real Unlock endpoint. *)
Lemma tmr_stop_nonrunning_return_post : forall context
  (before observed locked state_read unlocked : TmrStopState Application)
  status returned retcode error X heap,
  pointer <> 0 -> tmr_stop_type_program pooled index raw_type before 100 observed ->
  os_sched_lock_ints observed.(tmr_stop_kernel) <= 0 ->
  tmr_stop_lock_program critical sg effects context observed tt locked ->
  tmr_stop_state_program pooled index raw_state locked status state_read -> status <> 3 ->
  tmr_stop_nonrunning_output status = (retcode, error) ->
  tmr_stop_unlock_program external critical sg effects context state_read returned unlocked ->
  stop_safe context before X ->
  tmr_stop_owned returned (tmr_stop_set_error error unlocked) heap ->
  tmr_stop_post context before retcode X heap.
Proof.
  intros context before observed locked state_read unlocked status returned retcode error X heap
    Hpointer Htype Hints Hlock Hstate Hstatus Houtput Hunlock Hsafe Howned.
  eapply tmr_stop_source_return_post; [exact Hsafe| |exact Howned].
  unfold tmr_stop_call_result; cbn [tmr_stop_set_error tmr_stop_error].
  eapply tmr_stop_source_locked_return; [exact Hpointer|exact Htype|exact Hints|exact Hlock|].
  eapply tmr_stop_locked_nonrunning_step; [exact Hstatus|exact Hstate|].
  eapply tmr_stop_nonrunning_step; [exact Houtput|exact Hunlock].
Qed.

(** The final output is after.(error), not the zero written before the
    callback.  Neither a stopped image nor its callback/argument fields are
    retained as a postcondition after the callback has returned. *)
Lemma tmr_stop_running_return_post : forall context
  (before observed locked state_read stopped selected callback_after after : TmrStopState Application)
  request callback_returned returned X heap,
  pointer <> 0 -> tmr_stop_type_program pooled index raw_type before 100 observed ->
  os_sched_lock_ints observed.(tmr_stop_kernel) <= 0 ->
  tmr_stop_lock_program critical sg effects context observed tt locked ->
  tmr_stop_state_program pooled index raw_state locked 3 state_read ->
  tmr_stop_unlink_program sg index state_read tt stopped ->
  tmr_stop_select_callback_program pointer index opt argument
    (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped) request selected ->
  tmr_stop_optional_callback_program effects request context selected callback_returned callback_after ->
  tmr_stop_unlock_program external critical sg effects callback_returned callback_after returned after ->
  stop_safe context before X -> tmr_stop_owned returned after heap ->
  tmr_stop_post context before 1 X heap.
Proof.
  intros context before observed locked state_read stopped selected callback_after after
    request callback_returned returned X heap Hpointer Htype Hints Hlock Hstate Hunlink
    Hselect Hcallback Hunlock Hsafe Howned.
  eapply tmr_stop_source_return_post with (after := after) (returned := returned);
    [exact Hsafe| |exact Howned].
  unfold tmr_stop_call_result.
  eapply tmr_stop_source_locked_return with (observed := observed) (locked := locked);
    [exact Hpointer|exact Htype|exact Hints|exact Hlock|].
  eapply tmr_stop_locked_running_step with (observed := state_read); [exact Hstate|].
  exact (@tmr_stop_running_step Application external critical sg effects pointer index opt argument
    context state_read stopped request selected callback_returned callback_after returned after
    Hunlink Hselect Hcallback Hunlock).
Qed.

End PublicBranches.
End StopSpatial.
