Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_callback_registry_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From MonadLib.MonadErr Require Import MonadErrBasic.
Import TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** The approved normal-return observation permits suspension, while
    excluding outstanding event-pend status bits for the SAME caller.
    It is a callback source-proof obligation, never inferred from a
    pointer type, an empty registration pointer, or a current CPU token. *)
Definition tmr_task_caller_wait_status_clear (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  forall node,
    state.(TskState).(inUsedTaskStates)
      call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    task_non_suspension_bits node.(stat) = 0.

Lemma tmr_task_caller_wait_status_clear_from_ready : forall call state,
  os_sched_task_current_ready call state ->
  tmr_task_caller_wait_status_clear call state.
Proof.
  intros call state [current [[Hcurrent [Hid [Hcache [Hready Heffective]]]] Hgeneration]]
    node Hnode.
  assert (node = current) by congruence; subst node.
  apply task_effectively_ready_has_no_pending; exact Heffective.
Qed.

Lemma tmr_task_caller_wait_status_clear_same_call : forall first second state,
  task_tcb_init_stack_same_call second first ->
  tmr_task_caller_wait_status_clear first state ->
  tmr_task_caller_wait_status_clear second state.
Proof.
  intros first second state [_ [_ Hstack]] Hclear node Hnode.
  apply Hclear; rewrite Hstack in Hnode; exact Hnode.
Qed.

Section TaskClientStatusCallback.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  (mask perr : Z).

Definition tmr_task_client_status_callback_pre fn self argument context
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type)
  : TmrTaskFieldsRules.expr :=
  TmrTaskFieldsRules.andp
    (TmrTaskFieldsRules.coq_prop
      (arguments = (self, argument) /\
       tmr_task_callback_dispatch_domain sg fn self argument before /\
       tmr_task_fields_scan_ready sg before))
    (tmr_task_current_fields_owned AppRep environment sg mask perr context before).

Definition tmr_task_client_status_callback_return_facts fn self argument context
  (before : tmr_task_scan_world Application) returned after : Prop :=
  tmr_task_fields_callback_return_facts sg callback fn self argument context before returned after /\
  (tmr_task_caller_wait_status_clear context (fst before) ->
   tmr_task_caller_wait_status_clear returned (fst after)).

Definition tmr_task_client_status_callback_post fn self argument context
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type) (_ : unit)
  : TmrTaskFieldsRules.expr :=
  fun heap => exists returned after,
    arguments = (self, argument) /\
    tmr_task_client_status_callback_return_facts fn self argument context before returned after /\
    tmr_task_current_fields_owned AppRep environment sg mask perr returned after heap.

Definition tmr_task_client_status_callback_specification fn self argument
  : TmrTaskFieldsCallback.Spec TmrTaskFieldsCallback.timer_callback_signature :=
  fun body => @TmrTaskFieldsRules.allp OsSchedCallContext (fun context =>
    @TmrTaskFieldsRules.allp (tmr_task_scan_world Application) (fun before =>
      TmrTaskFieldsCallback.HoareFun TmrTaskFieldsCallback.timer_callback_signature
        (tmr_task_client_status_callback_pre fn self argument context before)
        (tmr_task_client_status_callback_post fn self argument context before) body)).

Definition tmr_task_client_status_callback_capability fn self argument : TmrTaskFieldsRules.expr :=
  @TmrTaskFieldsCallback.func_ptr_spec TmrTaskFieldsCallback.timer_callback_signature fn
    (tmr_task_client_status_callback_specification fn self argument).

Lemma tmr_task_client_status_callback_specification_environment_only : forall fn self argument,
  TmrTaskFieldsCallback.specification_environment_only
    (tmr_task_client_status_callback_specification fn self argument).
Proof.
  intros fn self argument; apply TmrTaskFieldsCallback.allp_specification_environment_only.
  intros ctx; apply TmrTaskFieldsCallback.allp_specification_environment_only.
  intros world; apply TmrTaskFieldsCallback.HoareFun_specification_environment_only.
Qed.

(** This is the only introduction rule here. Its evidence contains BOTH
    all-frame source Hoare safety and positive coverage of every source
    normal outcome. The new body preservation fields must be proved in
    that evidence; they cannot be registered from a type or a pure relation. *)
Lemma tmr_task_client_status_callback_capability_from_source : forall fn self argument
  (functions : TmrTaskFieldsCallback.callback_environment)
  (body : TmrTaskFieldsCallback.FunSem TmrTaskFieldsCallback.timer_callback_signature),
  fn <> 0 ->
  TmrTaskFieldsCallback.source_functions functions
    TmrTaskFieldsCallback.timer_callback_signature fn = Some body ->
  (forall context before,
    TmrTaskFieldsCallback.callback_source_evidence functions
      TmrTaskFieldsCallback.timer_callback_signature body
      (tmr_task_client_status_callback_pre fn self argument context before)
      (tmr_task_client_status_callback_post fn self argument context before)) ->
  forall heap, tmr_task_client_status_callback_capability fn self argument (heap, functions).
Proof.
  intros fn self argument functions body Hfn Hlookup Hsource heap.
  split; [exact Hfn|]. exists body; split; [exact Hlookup|].
  intros context before; exact (Hsource context before).
Qed.

Definition tmr_task_client_status_callback_call_pre fn self argument context
  (before : tmr_task_scan_world Application) (frame : TmrTaskFieldsRules.expr)
  : TmrTaskFieldsRules.expr :=
  @TmrTaskFieldsCallback.specified_call_pre TmrTaskFieldsCallback.timer_callback_signature
    fn (self, argument) (tmr_task_client_status_callback_specification fn self argument)
    (tmr_task_client_status_callback_pre fn self argument context before) frame.

Definition tmr_task_client_status_callback_call_post fn self argument context
  (before : tmr_task_scan_world Application) (frame : TmrTaskFieldsRules.expr)
  : unit -> TmrTaskFieldsRules.expr :=
  @TmrTaskFieldsCallback.specified_call_post TmrTaskFieldsCallback.timer_callback_signature
    fn (self, argument) (tmr_task_client_status_callback_specification fn self argument)
    (tmr_task_client_status_callback_post fn self argument context before) frame.

Lemma tmr_task_client_status_callback_call_pre_open : forall fn self argument context before frame,
  tmr_task_callback_dispatch_domain sg fn self argument before ->
  tmr_task_fields_scan_ready sg before ->
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.andp
      (TmrTaskFieldsRules.sepcon
        (tmr_task_current_fields_owned AppRep environment sg mask perr context before) frame)
      (tmr_task_client_status_callback_capability fn self argument))
    (tmr_task_client_status_callback_call_pre fn self argument context before frame).
Proof.
  intros fn self argument context before frame Hdomain Hready heap
    [[owned [rest [Hjoin [Howned Hframe]]]] Hcap].
  split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; [|exact Hframe].
  split; [|exact Howned]. split; [reflexivity|]. split; assumption.
Qed.

Definition tmr_task_client_status_callback_resume {Result : Type} fn self argument context
  (before : tmr_task_scan_world Application)
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) (frame : TmrTaskFieldsRules.expr)
  : TmrTaskFieldsRules.expr :=
  fun heap => exists returned after,
    tmr_task_client_status_callback_return_facts fn self argument context before returned after /\
    safeExec (eq after) (next returned) X /\
    TmrTaskFieldsRules.sepcon
      (tmr_task_current_fields_owned AppRep environment sg mask perr returned after) frame heap /\
    tmr_task_client_status_callback_capability fn self argument heap.

Lemma tmr_task_client_status_callback_call_post_continue : forall Result fn self argument context
  before (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame,
  safeExec (eq before)
    (StateRelMonad.bind (callback (fn, self, argument) context) next) X ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_status_callback_call_post fn self argument context before frame tt)
    (tmr_task_client_status_callback_resume fn self argument context before next X frame).
Proof.
  intros Result fn self argument context before next X frame Hsafe heap
    [[owned [rest [Hjoin [Hpost Hframe]]]] Hcap].
  destruct Hpost as [returned [after [Hargs [Hfacts Howned]]]].
  exists returned, after; split; [exact Hfacts|]. split.
  - eapply tmr_task_stage_continue; [exact (proj1 (proj1 Hfacts))|exact Hsafe].
  - split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; assumption.
Qed.

(** Same arbitrary X, same source call, and EVERY source normal memory
    outcome. The actual returned world/local is retained. No equality of
    task maps, old continuation families, or application states is used. *)
Theorem tmr_task_client_status_callback_call_rule : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame initial,
  safeExec (eq before)
    (StateRelMonad.bind (callback (fn, self, argument) context) next) X ->
  tmr_task_client_status_callback_call_pre fn self argument context before frame initial ->
  ~ @TmrTaskFieldsCallback.source_call_error TmrTaskFieldsCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) /\
  (forall final_memory,
    @TmrTaskFieldsCallback.source_call_normal TmrTaskFieldsCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) tt final_memory ->
    exists final,
      MonadErr.nrm (@TmrTaskFieldsCallback.indirect_call TmrTaskFieldsCallback.timer_callback_signature
        fn (self, argument)) initial tt final /\
      (fst final).(ConAssertion.s_mem) = final_memory /\
      tmr_task_client_status_callback_resume fn self argument context before next X frame final).
Proof.
  intros Result fn self argument context before next X frame initial Hsafe Hpre.
  assert (Hmatch : forall body, TmrTaskFieldsRules.derivable1
    (tmr_task_client_status_callback_specification fn self argument body)
    (TmrTaskFieldsCallback.HoareFun TmrTaskFieldsCallback.timer_callback_signature
      (tmr_task_client_status_callback_pre fn self argument context before)
      (tmr_task_client_status_callback_post fn self argument context before) body)).
  { intros body heap Hall; exact (Hall context before). }
  destruct (@TmrTaskFieldsCallback.indirect_call_specification_rule
    TmrTaskFieldsCallback.timer_callback_signature fn (self, argument)
    (tmr_task_client_status_callback_specification fn self argument)
    (tmr_task_client_status_callback_pre fn self argument context before)
    (tmr_task_client_status_callback_post fn self argument context before) frame
    (tmr_task_client_status_callback_specification_environment_only fn self argument) Hmatch)
    as [Hhoare Hcoverage].
  split.
  - intro Herror; exact (proj2 Hhoare initial Hpre Herror).
  - intros final_memory Hsource.
    destruct (Hcoverage initial tt final_memory Hpre Hsource)
      as [final [Hnormal [Hmemory Hpost]]].
    exists final; split; [exact Hnormal|]. split; [exact Hmemory|].
    exact (tmr_task_client_status_callback_call_post_continue Result fn self argument context
      before next X frame Hsafe final Hpost).
Qed.

(** Opening the returned owner exposes its OWN local family, at its OWN
    world. Supplemental padding stays in [frame] at its original index. *)
Lemma tmr_task_client_status_callback_resume_local : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame,
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_status_callback_resume fn self argument context before next X frame)
    (fun heap => exists returned after local,
      tmr_task_client_status_callback_return_facts fn self argument context before returned after /\
      safeExec (eq after) (next returned) X /\
      TmrTaskFieldsRules.sepcon
        (tmr_task_fields_owned AppRep environment sg mask perr local returned after) frame heap /\
      tmr_task_client_status_callback_capability fn self argument heap).
Proof.
  intros Result fn self argument context before next X frame heap
    [returned [after [Hfacts [Hsafe [[owned [rest [Hjoin [[local Howned] Hframe]]]] Hcap]]]]].
  exists returned, after, local; split; [exact Hfacts|]. split; [exact Hsafe|].
  split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; assumption.
Qed.

Lemma tmr_task_client_status_callback_post_forget_status : forall fn self argument context
  before arguments result,
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_status_callback_post fn self argument context before arguments result)
    (tmr_task_fields_callback_post AppRep environment sg callback mask perr
      fn self argument context before arguments result).
Proof.
  intros fn self argument context before arguments result heap
    [returned [after [Hargs [[Hfacts Hstatus] Howned]]]].
  exists returned, after; exact (conj Hargs (conj Hfacts Howned)).
Qed.

Lemma tmr_task_client_status_callback_capability_forget_status : forall fn self argument,
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_status_callback_capability fn self argument)
    (tmr_task_fields_callback_capability AppRep environment sg callback mask perr
      fn self argument).
Proof.
  intros fn self argument; apply TmrTaskFieldsCallback.func_ptr_spec_mono.
  intros body heap Hspec context before.
  eapply (@TmrTaskFieldsCallback.HoareFun_conseq TmrTaskFieldsCallback.timer_callback_signature
    (tmr_task_client_status_callback_pre fn self argument context before)
    (tmr_task_fields_callback_pre AppRep environment sg mask perr fn self argument context before)
    (tmr_task_client_status_callback_post fn self argument context before)
    (tmr_task_fields_callback_post AppRep environment sg callback mask perr fn self argument context before)).
  - intros arguments owned Hpre; exact Hpre.
  - intros arguments result; apply tmr_task_client_status_callback_post_forget_status.
  - exact (Hspec context before).
Qed.

Lemma tmr_task_client_status_callback_resume_status : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame,
  tmr_task_caller_wait_status_clear context (fst before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_client_status_callback_resume fn self argument context before next X frame)
    (fun heap => exists returned after,
      tmr_task_fields_callback_return_facts sg callback fn self argument context before returned after /\
      tmr_task_caller_wait_status_clear returned (fst after) /\
      safeExec (eq after) (next returned) X /\
      TmrTaskFieldsRules.sepcon
        (tmr_task_current_fields_owned AppRep environment sg mask perr returned after) frame heap /\
      tmr_task_client_status_callback_capability fn self argument heap).
Proof.
  intros Result fn self argument context before next X frame Hclear heap
    [returned [after [[Hfacts Hstatus] [Hsafe [Howned Hcap]]]]].
  exists returned, after.
  exact (conj Hfacts (conj (Hstatus Hclear) (conj Hsafe (conj Howned Hcap)))).
Qed.

End TaskClientStatusCallback.

Section TaskClientStatusCallbackRegistry.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  (mask : Z) (initial_context : OsSchedCallContext)
  (initial_world : tmr_task_scan_world Application).

Definition tmr_task_client_status_callback_domain fn self argument context
  (world : tmr_task_scan_world Application) : Prop :=
  exists history visited current cursor index tail future cached dispatched,
    tmr_task_client_history environment critical sg mask
      (tmr_task_framed_effects callback) initial_context initial_world history /\
    tmr_task_scan_prefix sg callback (tmr_task_continuation_spoke sg history)
      (tmr_task_continuation_start history) history.(tmr_task_continuation_lock_context)
      (tmr_task_continuation_scan sg history) visited current context cursor /\
    cursor.(timerScanRemaining) = index :: tail /\
    timer_scan_advance (tmr_task_timers current) cursor = Some future /\
    timer_expire_dispatch sg (tmr_task_timers current) index =
      Some (cached, Some (fn, self, argument), dispatched) /\
    world = tmr_task_set_timers dispatched current.

Lemma tmr_task_client_status_callback_domain_from_prefix : forall history visited current context
  cursor index tail future cached dispatched fn self argument,
  tmr_task_client_history environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial_world history ->
  tmr_task_scan_prefix sg callback (tmr_task_continuation_spoke sg history)
    (tmr_task_continuation_start history) history.(tmr_task_continuation_lock_context)
    (tmr_task_continuation_scan sg history) visited current context cursor ->
  cursor.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers current) cursor = Some future ->
  timer_expire_dispatch sg (tmr_task_timers current) index =
    Some (cached, Some (fn, self, argument), dispatched) ->
  tmr_task_client_status_callback_domain fn self argument context
    (tmr_task_set_timers dispatched current).
Proof.
  intros history visited current context cursor index tail future cached dispatched
    fn self argument Hhistory Hprefix Hremaining Hadvance Hdispatch.
  exists history, visited, current, cursor, index, tail, future, cached, dispatched.
  split; [exact Hhistory|]. split; [exact Hprefix|]. split; [exact Hremaining|].
  split; [exact Hadvance|]. split; [exact Hdispatch|reflexivity].
Qed.

Lemma tmr_task_client_status_callback_domain_from_scan : forall history visited current context
  cursor index tail future cached dispatched fn self argument X,
  tmr_task_client_scan_facts environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial_world history visited
    context current cursor X ->
  cursor.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers current) cursor = Some future ->
  timer_expire_dispatch sg (tmr_task_timers current) index =
    Some (cached, Some (fn, self, argument), dispatched) ->
  tmr_task_client_status_callback_domain fn self argument context
    (tmr_task_set_timers dispatched current).
Proof.
  intros history visited current context cursor index tail future cached dispatched
    fn self argument X [Hhistory [Hprefix Hrest]] Hremaining Hadvance Hdispatch.
  eapply tmr_task_client_status_callback_domain_from_prefix; eassumption.
Qed.

Definition tmr_task_client_status_callback_capabilities : TmrTaskFieldsRules.expr :=
  fun heap => forall perr fn self argument context world,
    tmr_task_client_status_callback_domain fn self argument context world ->
    tmr_task_client_status_callback_capability AppRep environment sg callback mask perr
      fn self argument heap.

Lemma tmr_task_client_status_callback_capabilities_selected : forall perr fn self argument context world,
  tmr_task_client_status_callback_domain fn self argument context world ->
  TmrTaskFieldsRules.derivable1 tmr_task_client_status_callback_capabilities
    (tmr_task_client_status_callback_capability AppRep environment sg callback mask perr
      fn self argument).
Proof.
  intros perr fn self argument context world Hdomain heap Hcaps.
  exact (Hcaps perr fn self argument context world Hdomain).
Qed.

Lemma tmr_task_client_status_callback_capabilities_environment_only :
  TmrTaskFieldsCallback.assertion_environment_only tmr_task_client_status_callback_capabilities.
Proof.
  intros first second Henv Hcaps perr fn self argument context world Hdomain.
  apply (@TmrTaskFieldsCallback.func_ptr_spec_environment_eq
    TmrTaskFieldsCallback.timer_callback_signature fn
    (tmr_task_client_status_callback_specification AppRep environment sg callback mask perr
      fn self argument)
    (tmr_task_client_status_callback_specification_environment_only AppRep environment sg
      callback mask perr fn self argument) first second Henv).
  exact (Hcaps perr fn self argument context world Hdomain).
Qed.

Lemma tmr_task_client_status_callback_capabilities_join : forall first frame combined,
  TmrTaskFieldsRules.join first frame combined ->
  (tmr_task_client_status_callback_capabilities first <->
   tmr_task_client_status_callback_capabilities combined).
Proof.
  intros first frame combined Hjoin.
  change (UCOS2_C_Rules.join (fst first) (fst frame) (fst combined) /\
    snd first = snd combined /\ snd frame = snd combined) in Hjoin.
  destruct Hjoin as [_ [Henv _]]; split; intro Hcaps.
  - exact (tmr_task_client_status_callback_capabilities_environment_only first combined Henv Hcaps).
  - apply (tmr_task_client_status_callback_capabilities_environment_only combined first).
    + symmetry; exact Henv.
    + exact Hcaps.
Qed.

Lemma tmr_task_client_status_callback_capabilities_split : forall resources,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.andp resources tmr_task_client_status_callback_capabilities)
    (TmrTaskFieldsRules.sepcon resources tmr_task_client_status_callback_capabilities).
Proof.
  intros resources heap [Hresources Hcaps].
  destruct (TmrTaskFieldsRules.unit_join heap) as [unit [Hunit Hjoin]].
  exists heap, unit; split; [exact Hjoin|]. split; [exact Hresources|].
  apply (proj2 (tmr_task_client_status_callback_capabilities_join unit heap heap
    (TmrTaskFieldsRules.join_comm heap unit heap Hjoin))); exact Hcaps.
Qed.

Lemma tmr_task_client_status_callback_capabilities_indirect_return : forall fn self argument before after,
  MonadErr.nrm (@TmrTaskFieldsCallback.indirect_call
    TmrTaskFieldsCallback.timer_callback_signature fn (self, argument)) before tt after ->
  tmr_task_client_status_callback_capabilities before ->
  tmr_task_client_status_callback_capabilities after.
Proof.
  intros fn self argument before after Hcall Hcaps.
  apply (tmr_task_client_status_callback_capabilities_environment_only before after).
  - symmetry; exact (@TmrTaskFieldsCallback.indirect_call_preserves_environment
      TmrTaskFieldsCallback.timer_callback_signature fn (self, argument) before after tt Hcall).
  - exact Hcaps.
Qed.

Lemma tmr_task_client_status_callback_capabilities_from_source : forall
  (functions : TmrTaskFieldsCallback.callback_environment),
  (forall perr fn self argument,
    (exists context world, tmr_task_client_status_callback_domain fn self argument context world) ->
    exists body,
      fn <> 0 /\
      TmrTaskFieldsCallback.source_functions functions
        TmrTaskFieldsCallback.timer_callback_signature fn = Some body /\
      forall context world,
        TmrTaskFieldsCallback.callback_source_evidence functions
          TmrTaskFieldsCallback.timer_callback_signature body
          (tmr_task_client_status_callback_pre AppRep environment sg mask perr
            fn self argument context world)
          (tmr_task_client_status_callback_post AppRep environment sg callback mask perr
            fn self argument context world)) ->
  forall heap, tmr_task_client_status_callback_capabilities (heap, functions).
Proof.
  intros functions Hsources heap perr fn self argument context world Hdomain.
  destruct (Hsources perr fn self argument (ex_intro _ context (ex_intro _ world Hdomain)))
    as [body [Hnonnull [Hlookup Hevidence]]].
  apply (tmr_task_client_status_callback_capability_from_source AppRep environment sg callback
    mask perr fn self argument functions body Hnonnull Hlookup Hevidence heap).
Qed.

Definition tmr_task_client_status_prefix_registered (registered : addr -> Prop) : Prop :=
  forall fn self argument context world,
    tmr_task_client_status_callback_domain fn self argument context world -> registered fn.

(** Registered addresses and the complete client-history domain remain
    arbitrary. Each actual body must now prove the additional approved
    return-status property; an old weaker capability cannot supply it. *)
Definition tmr_task_client_status_registered_sources (registered : addr -> Prop)
  (functions : TmrTaskFieldsCallback.callback_environment) : Prop :=
  forall fn, registered fn -> exists body,
    fn <> 0 /\
    TmrTaskFieldsCallback.source_functions functions
      TmrTaskFieldsCallback.timer_callback_signature fn = Some body /\
    forall perr self argument context world,
      TmrTaskFieldsCallback.callback_source_evidence functions
        TmrTaskFieldsCallback.timer_callback_signature body
        (tmr_task_client_status_callback_pre AppRep environment sg mask perr
          fn self argument context world)
        (tmr_task_client_status_callback_post AppRep environment sg callback mask perr
          fn self argument context world).


Lemma tmr_task_client_status_callback_capabilities_from_registry : forall registered functions,
  tmr_task_client_status_registered_sources registered functions ->
  tmr_task_client_status_prefix_registered registered ->
  forall heap, tmr_task_client_status_callback_capabilities (heap, functions).
Proof.
  intros registered functions Hsources Hmembers.
  apply tmr_task_client_status_callback_capabilities_from_source.
  intros perr fn self argument [context [world Hdomain]].
  destruct (Hsources fn (Hmembers fn self argument context world Hdomain))
    as [body [Hnonnull [Hlookup Hevidence]]].
  exists body; split; [exact Hnonnull|]. split; [exact Hlookup|].
  intros current_context current_world; apply Hevidence.
Qed.

End TaskClientStatusCallbackRegistry.
