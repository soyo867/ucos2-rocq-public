Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_registry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_client_annotation_spec.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
From MonadLib.MonadErr Require Import MonadErrBasic.
Import ListNotations.
Local Open Scope Z_scope.

(** The client-level Pend changes the source history of reachable calls.
    The actual callback pre/post, typed source evidence and arbitrary
    function addresses remain those of the existing fields contract.
    Capabilities on the older, smaller history domain do not imply these
    capabilities. The source producer below uses the original registered
    bodies and membership of the actual client-level execution. *)
Section TaskClientCallbackRegistry.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  (mask : Z) (initial_context : OsSchedCallContext)
  (initial_world : tmr_task_scan_world Application).

Definition tmr_task_client_callback_domain fn self argument context
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

Lemma tmr_task_client_callback_domain_from_prefix : forall history visited current context
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
  tmr_task_client_callback_domain fn self argument context
    (tmr_task_set_timers dispatched current).
Proof.
  intros history visited current context cursor index tail future cached dispatched
    fn self argument Hhistory Hprefix Hremaining Hadvance Hdispatch.
  exists history, visited, current, cursor, index, tail, future, cached, dispatched.
  split; [exact Hhistory|]. split; [exact Hprefix|]. split; [exact Hremaining|].
  split; [exact Hadvance|]. split; [exact Hdispatch|reflexivity].
Qed.

Lemma tmr_task_client_callback_domain_from_scan : forall history visited current context
  cursor index tail future cached dispatched fn self argument X,
  tmr_task_client_scan_facts environment critical sg mask
    (tmr_task_framed_effects callback) initial_context initial_world history visited
    context current cursor X ->
  cursor.(timerScanRemaining) = index :: tail ->
  timer_scan_advance (tmr_task_timers current) cursor = Some future ->
  timer_expire_dispatch sg (tmr_task_timers current) index =
    Some (cached, Some (fn, self, argument), dispatched) ->
  tmr_task_client_callback_domain fn self argument context
    (tmr_task_set_timers dispatched current).
Proof.
  intros history visited current context cursor index tail future cached dispatched
    fn self argument X [Hhistory [Hprefix Hrest]] Hremaining Hadvance Hdispatch.
  eapply tmr_task_client_callback_domain_from_prefix; eassumption.
Qed.

Definition tmr_task_client_callback_capabilities : TmrTaskFieldsRules.expr :=
  fun heap => forall perr fn self argument context world,
    tmr_task_client_callback_domain fn self argument context world ->
    tmr_task_fields_callback_capability AppRep environment sg callback mask perr
      fn self argument heap.

Lemma tmr_task_client_callback_capabilities_selected : forall perr fn self argument context world,
  tmr_task_client_callback_domain fn self argument context world ->
  TmrTaskFieldsRules.derivable1 tmr_task_client_callback_capabilities
    (tmr_task_fields_callback_capability AppRep environment sg callback mask perr
      fn self argument).
Proof.
  intros perr fn self argument context world Hdomain heap Hcaps.
  exact (Hcaps perr fn self argument context world Hdomain).
Qed.

Lemma tmr_task_client_callback_capabilities_environment_only :
  TmrTaskFieldsCallback.assertion_environment_only tmr_task_client_callback_capabilities.
Proof.
  intros first second Henv Hcaps perr fn self argument context world Hdomain.
  apply (@TmrTaskFieldsCallback.func_ptr_spec_environment_eq
    TmrTaskFieldsCallback.timer_callback_signature fn
    (tmr_task_fields_callback_specification AppRep environment sg callback mask perr
      fn self argument)
    (tmr_task_fields_callback_specification_environment_only AppRep environment sg
      callback mask perr fn self argument) first second Henv).
  exact (Hcaps perr fn self argument context world Hdomain).
Qed.

Lemma tmr_task_client_callback_capabilities_join : forall first frame combined,
  TmrTaskFieldsRules.join first frame combined ->
  (tmr_task_client_callback_capabilities first <->
   tmr_task_client_callback_capabilities combined).
Proof.
  intros first frame combined Hjoin.
  change (UCOS2_C_Rules.join (fst first) (fst frame) (fst combined) /\
    snd first = snd combined /\ snd frame = snd combined) in Hjoin.
  destruct Hjoin as [_ [Henv _]]; split; intro Hcaps.
  - exact (tmr_task_client_callback_capabilities_environment_only first combined Henv Hcaps).
  - apply (tmr_task_client_callback_capabilities_environment_only combined first).
    + symmetry; exact Henv.
    + exact Hcaps.
Qed.

Lemma tmr_task_client_callback_capabilities_split : forall resources,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.andp resources tmr_task_client_callback_capabilities)
    (TmrTaskFieldsRules.sepcon resources tmr_task_client_callback_capabilities).
Proof.
  intros resources heap [Hresources Hcaps].
  destruct (TmrTaskFieldsRules.unit_join heap) as [unit [Hunit Hjoin]].
  exists heap, unit; split; [exact Hjoin|]. split; [exact Hresources|].
  apply (proj2 (tmr_task_client_callback_capabilities_join unit heap heap
    (TmrTaskFieldsRules.join_comm heap unit heap Hjoin))); exact Hcaps.
Qed.

Lemma tmr_task_client_callback_capabilities_indirect_return : forall fn self argument before after,
  MonadErr.nrm (@TmrTaskFieldsCallback.indirect_call
    TmrTaskFieldsCallback.timer_callback_signature fn (self, argument)) before tt after ->
  tmr_task_client_callback_capabilities before ->
  tmr_task_client_callback_capabilities after.
Proof.
  intros fn self argument before after Hcall Hcaps.
  apply (tmr_task_client_callback_capabilities_environment_only before after).
  - symmetry; exact (@TmrTaskFieldsCallback.indirect_call_preserves_environment
      TmrTaskFieldsCallback.timer_callback_signature fn (self, argument) before after tt Hcall).
  - exact Hcaps.
Qed.

Lemma tmr_task_client_callback_capabilities_from_source : forall
  (functions : TmrTaskFieldsCallback.callback_environment),
  (forall perr fn self argument,
    (exists context world, tmr_task_client_callback_domain fn self argument context world) ->
    exists body,
      fn <> 0 /\
      TmrTaskFieldsCallback.source_functions functions
        TmrTaskFieldsCallback.timer_callback_signature fn = Some body /\
      forall context world,
        TmrTaskFieldsCallback.callback_source_evidence functions
          TmrTaskFieldsCallback.timer_callback_signature body
          (tmr_task_fields_callback_pre AppRep environment sg mask perr
            fn self argument context world)
          (tmr_task_fields_callback_post AppRep environment sg callback mask perr
            fn self argument context world)) ->
  forall heap, tmr_task_client_callback_capabilities (heap, functions).
Proof.
  intros functions Hsources heap perr fn self argument context world Hdomain.
  destruct (Hsources perr fn self argument (ex_intro _ context (ex_intro _ world Hdomain)))
    as [body [Hnonnull [Hlookup Hevidence]]].
  apply (tmr_task_fields_callback_capability_from_source AppRep environment sg callback
    mask perr fn self argument functions body Hnonnull Hlookup Hevidence heap).
Qed.

Definition tmr_task_client_prefix_registered (registered : addr -> Prop) : Prop :=
  forall fn self argument context world,
    tmr_task_client_callback_domain fn self argument context world -> registered fn.

(** The source registry is unchanged: it already quantifies over every
    actual callback context/world. The remaining membership obligation is
    for the new reachable history, not the old restricted history. *)
Lemma tmr_task_client_callback_capabilities_from_registry : forall registered functions,
  tmr_task_fields_registered_sources AppRep environment sg callback mask registered functions ->
  tmr_task_client_prefix_registered registered ->
  forall heap, tmr_task_client_callback_capabilities (heap, functions).
Proof.
  intros registered functions Hsources Hmembers.
  apply tmr_task_client_callback_capabilities_from_source.
  intros perr fn self argument [context [world Hdomain]].
  destruct (Hsources fn (Hmembers fn self argument context world Hdomain))
    as [body [Hnonnull [Hlookup Hevidence]]].
  exists body; split; [exact Hnonnull|]. split; [exact Hlookup|].
  intros current_context current_world; apply Hevidence.
Qed.

End TaskClientCallbackRegistry.
