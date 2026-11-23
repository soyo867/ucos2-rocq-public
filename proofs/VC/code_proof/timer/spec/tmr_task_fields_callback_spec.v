Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fresh_fields_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_task_scheduler_adapter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_loop_program_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_next_pend_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From MonadLib.MonadErr Require Import MonadErrBasic.

Import TaskStateDef ListNotations.
Local Open Scope Z_scope.
Module TmrTaskFieldsCallback := TimerCallback_C_Rules.

(** These are observations of the actual caller node, not a ready-state
    invariant. Source liveness supplies the node; this predicate supplies
    its non-Idle/clear-wait fields. In particular, Multi=0 configuration
    alone does not establish the abstract multi pointer's value. *)
Definition tmr_task_fields_caller_clear sg call state : Prop :=
  forall node,
    state.(TskState).(inUsedTaskStates)
      call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(curPrio) <> sg.(osLowestPrio) /\
    flag_active_event_clear node /\ node.(tcbFlagNode) = 0.

Lemma tmr_task_fields_caller_clear_from_pend : forall sg call state,
  sem_pend_task_call_stage sg call state ->
  (forall node,
    state.(TskState).(inUsedTaskStates)
      call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(tcbEventMultiPtr) = 0) ->
  tmr_task_fields_caller_clear sg call state.
Proof.
  intros sg call state [_ [_ [current [Hready [Hgen [Hnonidle [Hevent [Hmulti Hflag]]]]]]]]
    Hptr node Hnode.
  assert (node = current) by (pose proof (proj1 Hready); congruence); subst node.
  split; [exact Hnonidle|]. split; [|exact Hflag].
  split; [exact Hevent|]. split; [exact Hmulti|].
  apply Hptr; exact (proj1 Hready).
Qed.

Lemma tmr_task_fields_caller_clear_fresh : forall sg call state,
  kernel_call_task_source call state ->
  tmr_task_fields_caller_clear sg call state ->
  flag_active_fresh_registration call call state.
Proof.
  intros sg call state Hsource Hfields.
  destruct (kernel_call_task_source_current_at call state Hsource)
    as [Hcurrent [node [Hnode Hgen]]].
  destruct (Hfields node Hnode) as [Hnonidle [Hclear Hflag]].
  eapply os_sched_unlock_source_fresh_registration; eassumption.
Qed.

Lemma tmr_task_fields_caller_clear_pend_stage : forall sg call state,
  kernel_call_task_source call state -> state.(SchedState).(isRunning) = true ->
  os_sched_task_current_ready call state ->
  tmr_task_fields_caller_clear sg call state ->
  sem_pend_task_call_stage sg call state.
Proof.
  intros sg call state Hsource Hrunning Hready Hfields.
  eapply tmr_task_pend_stage_from_current_ready; try eassumption.
  intros node Hnode; destruct (Hfields node Hnode) as [Hnonidle [[Hevent [Hmulti Hptr]] Hflag]].
  split; [exact Hnonidle|]. unfold sem_pend_task_unregistered; repeat split; assumption.
Qed.

(** Enrollment obligations for one concrete callback BODY and
    its authorized callees/environment. They are not implied by the C
    function-pointer type or by the public Timer documentation. Keeping
    them conditional avoids inventing initial source/Idle/clear fields.

    This record permits changes to other tasks, ready lists, application
    state, Timer objects, and the signal's public type/generation. Its public
    signal field excludes ONLY a private/unpublished slot at the current
    endpoint. NULL is unguarded; public FREE and wrong-type slots remain.
    Current priority consistency must be preserved by the actual callback
    body, including calls that change the current task's priority.
    No field asserts current readiness or safety at future acquisitions. *)
Record tmr_task_fields_callback_preserves sg original before returned after : Prop := {
  tmr_task_fields_callback_preserves_source :
    kernel_call_task_source original before -> kernel_call_task_source returned after;
  tmr_task_fields_callback_preserves_available :
    kernel_call_stack_available original before -> kernel_call_stack_available returned after;
  tmr_task_fields_callback_preserves_running :
    before.(SchedState).(isRunning) = true -> after.(SchedState).(isRunning) = true;
  tmr_task_fields_callback_preserves_clear :
    tmr_task_fields_caller_clear sg original before -> tmr_task_fields_caller_clear sg returned after;
  tmr_task_fields_callback_preserves_idle :
    task_idle_ready sg before.(TskState) -> task_idle_ready sg after.(TskState);
  tmr_task_fields_callback_preserves_public_signal :
    forall eid observed,
    before.(TimerState).(timerSignalSem) <> 0 ->
    before.(TimerState).(timerSignalSem) = event_addr sg eid ->
    sem_query_public_slot before eid observed ->
    exists current, sem_query_public_slot after eid current;
  tmr_task_fields_callback_preserves_current_consistency :
    sched_current_consistency before.(TskState) before.(SchedState) ->
    sched_current_consistency after.(TskState) after.(SchedState)
}.

Definition tmr_task_fields_scan_ready {Application}
  sg (world : tmr_task_scan_world Application) : Prop :=
  valid_timer_state sg (tmr_task_timers world) /\
  timer_api_initialized (tmr_task_timers world).

Section TaskFieldsCallbackContract.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  (mask perr : Z).

(** The precondition uses the actual expiration dispatch domain. The
    capability is still quantified over EVERY context and world, rather
    than specialized to one call or restricted to a list of callbacks. *)
Definition tmr_task_fields_callback_pre fn self argument context
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type)
  : TmrTaskFieldsRules.expr :=
  TmrTaskFieldsRules.andp
    (TmrTaskFieldsRules.coq_prop
      (arguments = (self, argument) /\
       tmr_task_callback_dispatch_domain sg fn self argument before /\
       tmr_task_fields_scan_ready sg before))
    (tmr_task_current_fields_owned AppRep environment sg mask perr context before).

Definition tmr_task_fields_callback_return_facts fn self argument context
  (before : tmr_task_scan_world Application) returned after : Prop :=
  callback (fn, self, argument) context before returned after /\
  tmr_task_fields_scan_ready sg after /\
  tmr_task_service_frame (tmr_task_timers before) (tmr_task_timers after) /\
  kernel_stack_call_same_call returned context /\
  tmr_task_fields_callback_preserves sg context (fst before) returned (fst after).

Definition tmr_task_fields_callback_post fn self argument context
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type) (_ : unit)
  : TmrTaskFieldsRules.expr :=
  fun heap => exists returned after,
    arguments = (self, argument) /\
    tmr_task_fields_callback_return_facts fn self argument context before returned after /\
    tmr_task_current_fields_owned AppRep environment sg mask perr returned after heap.

Definition tmr_task_fields_callback_specification fn self argument
  : TmrTaskFieldsCallback.Spec TmrTaskFieldsCallback.timer_callback_signature :=
  fun body => @TmrTaskFieldsRules.allp OsSchedCallContext (fun context =>
    @TmrTaskFieldsRules.allp (tmr_task_scan_world Application) (fun before =>
      TmrTaskFieldsCallback.HoareFun TmrTaskFieldsCallback.timer_callback_signature
        (tmr_task_fields_callback_pre fn self argument context before)
        (tmr_task_fields_callback_post fn self argument context before) body)).

Definition tmr_task_fields_callback_capability fn self argument : TmrTaskFieldsRules.expr :=
  @TmrTaskFieldsCallback.func_ptr_spec TmrTaskFieldsCallback.timer_callback_signature fn
    (tmr_task_fields_callback_specification fn self argument).

Lemma tmr_task_fields_callback_specification_environment_only : forall fn self argument,
  TmrTaskFieldsCallback.specification_environment_only
    (tmr_task_fields_callback_specification fn self argument).
Proof.
  intros fn self argument; apply TmrTaskFieldsCallback.allp_specification_environment_only.
  intros ctx; apply TmrTaskFieldsCallback.allp_specification_environment_only.
  intros world; apply TmrTaskFieldsCallback.HoareFun_specification_environment_only.
Qed.

(** This is the only introduction rule here. Its evidence contains BOTH
    all-frame source Hoare safety and positive coverage of every source
    normal outcome. The new body preservation fields must be proved in
    that evidence; they cannot be registered from a type or a pure relation. *)
Lemma tmr_task_fields_callback_capability_from_source : forall fn self argument
  (functions : TmrTaskFieldsCallback.callback_environment)
  (body : TmrTaskFieldsCallback.FunSem TmrTaskFieldsCallback.timer_callback_signature),
  fn <> 0 ->
  TmrTaskFieldsCallback.source_functions functions
    TmrTaskFieldsCallback.timer_callback_signature fn = Some body ->
  (forall context before,
    TmrTaskFieldsCallback.callback_source_evidence functions
      TmrTaskFieldsCallback.timer_callback_signature body
      (tmr_task_fields_callback_pre fn self argument context before)
      (tmr_task_fields_callback_post fn self argument context before)) ->
  forall heap, tmr_task_fields_callback_capability fn self argument (heap, functions).
Proof.
  intros fn self argument functions body Hfn Hlookup Hsource heap.
  split; [exact Hfn|]. exists body; split; [exact Hlookup|].
  intros context before; exact (Hsource context before).
Qed.

Definition tmr_task_fields_callback_call_pre fn self argument context
  (before : tmr_task_scan_world Application) (frame : TmrTaskFieldsRules.expr)
  : TmrTaskFieldsRules.expr :=
  @TmrTaskFieldsCallback.specified_call_pre TmrTaskFieldsCallback.timer_callback_signature
    fn (self, argument) (tmr_task_fields_callback_specification fn self argument)
    (tmr_task_fields_callback_pre fn self argument context before) frame.

Definition tmr_task_fields_callback_call_post fn self argument context
  (before : tmr_task_scan_world Application) (frame : TmrTaskFieldsRules.expr)
  : unit -> TmrTaskFieldsRules.expr :=
  @TmrTaskFieldsCallback.specified_call_post TmrTaskFieldsCallback.timer_callback_signature
    fn (self, argument) (tmr_task_fields_callback_specification fn self argument)
    (tmr_task_fields_callback_post fn self argument context before) frame.

Lemma tmr_task_fields_callback_call_pre_open : forall fn self argument context before frame,
  tmr_task_callback_dispatch_domain sg fn self argument before ->
  tmr_task_fields_scan_ready sg before ->
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.andp
      (TmrTaskFieldsRules.sepcon
        (tmr_task_current_fields_owned AppRep environment sg mask perr context before) frame)
      (tmr_task_fields_callback_capability fn self argument))
    (tmr_task_fields_callback_call_pre fn self argument context before frame).
Proof.
  intros fn self argument context before frame Hdomain Hready heap
    [[owned [rest [Hjoin [Howned Hframe]]]] Hcap].
  split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; [|exact Hframe].
  split; [|exact Howned]. split; [reflexivity|]. split; assumption.
Qed.

Definition tmr_task_fields_callback_resume {Result : Type} fn self argument context
  (before : tmr_task_scan_world Application)
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) (frame : TmrTaskFieldsRules.expr)
  : TmrTaskFieldsRules.expr :=
  fun heap => exists returned after,
    tmr_task_fields_callback_return_facts fn self argument context before returned after /\
    safeExec (eq after) (next returned) X /\
    TmrTaskFieldsRules.sepcon
      (tmr_task_current_fields_owned AppRep environment sg mask perr returned after) frame heap /\
    tmr_task_fields_callback_capability fn self argument heap.

Lemma tmr_task_fields_callback_call_post_continue : forall Result fn self argument context
  before (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame,
  safeExec (eq before)
    (StateRelMonad.bind (callback (fn, self, argument) context) next) X ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_call_post fn self argument context before frame tt)
    (tmr_task_fields_callback_resume fn self argument context before next X frame).
Proof.
  intros Result fn self argument context before next X frame Hsafe heap
    [[owned [rest [Hjoin [Hpost Hframe]]]] Hcap].
  destruct Hpost as [returned [after [Hargs [Hfacts Howned]]]].
  exists returned, after; split; [exact Hfacts|]. split.
  - eapply tmr_task_stage_continue; [exact (proj1 Hfacts)|exact Hsafe].
  - split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; assumption.
Qed.

(** Same arbitrary X, same source call, and EVERY source normal memory
    outcome. The actual returned world/local is retained. No equality of
    task maps, old continuation families, or application states is used. *)
Theorem tmr_task_fields_callback_call_rule : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame initial,
  safeExec (eq before)
    (StateRelMonad.bind (callback (fn, self, argument) context) next) X ->
  tmr_task_fields_callback_call_pre fn self argument context before frame initial ->
  ~ @TmrTaskFieldsCallback.source_call_error TmrTaskFieldsCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) /\
  (forall final_memory,
    @TmrTaskFieldsCallback.source_call_normal TmrTaskFieldsCallback.timer_callback_signature
      (snd initial) fn (self, argument) (fst initial).(ConAssertion.s_mem) tt final_memory ->
    exists final,
      MonadErr.nrm (@TmrTaskFieldsCallback.indirect_call TmrTaskFieldsCallback.timer_callback_signature
        fn (self, argument)) initial tt final /\
      (fst final).(ConAssertion.s_mem) = final_memory /\
      tmr_task_fields_callback_resume fn self argument context before next X frame final).
Proof.
  intros Result fn self argument context before next X frame initial Hsafe Hpre.
  assert (Hmatch : forall body, TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_specification fn self argument body)
    (TmrTaskFieldsCallback.HoareFun TmrTaskFieldsCallback.timer_callback_signature
      (tmr_task_fields_callback_pre fn self argument context before)
      (tmr_task_fields_callback_post fn self argument context before) body)).
  { intros body heap Hall; exact (Hall context before). }
  destruct (@TmrTaskFieldsCallback.indirect_call_specification_rule
    TmrTaskFieldsCallback.timer_callback_signature fn (self, argument)
    (tmr_task_fields_callback_specification fn self argument)
    (tmr_task_fields_callback_pre fn self argument context before)
    (tmr_task_fields_callback_post fn self argument context before) frame
    (tmr_task_fields_callback_specification_environment_only fn self argument) Hmatch)
    as [Hhoare Hcoverage].
  split.
  - intro Herror; exact (proj2 Hhoare initial Hpre Herror).
  - intros final_memory Hsource.
    destruct (Hcoverage initial tt final_memory Hpre Hsource)
      as [final [Hnormal [Hmemory Hpost]]].
    exists final; split; [exact Hnormal|]. split; [exact Hmemory|].
    exact (tmr_task_fields_callback_call_post_continue Result fn self argument context
      before next X frame Hsafe final Hpost).
Qed.

(** Opening the returned owner exposes its OWN local family, at its OWN
    world. Supplemental padding stays in [frame] at its original index. *)
Lemma tmr_task_fields_callback_resume_local : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame,
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_resume fn self argument context before next X frame)
    (fun heap => exists returned after local,
      tmr_task_fields_callback_return_facts fn self argument context before returned after /\
      safeExec (eq after) (next returned) X /\
      TmrTaskFieldsRules.sepcon
        (tmr_task_fields_owned AppRep environment sg mask perr local returned after) frame heap /\
      tmr_task_fields_callback_capability fn self argument heap).
Proof.
  intros Result fn self argument context before next X frame heap
    [returned [after [Hfacts [Hsafe [[owned [rest [Hjoin [[local Howned] Hframe]]]] Hcap]]]]].
  exists returned, after, local; split; [exact Hfacts|]. split; [exact Hsafe|].
  split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; assumption.
Qed.

(** The repaired scan consumes the current spoke head, retaining the
    complete endpoint facts, current resources, and continuation with X. *)
Lemma tmr_task_fields_callback_resume_reload : forall Result fn self argument context before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame spoke,
  tmr_task_spoke_in_range sg spoke ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_resume fn self argument context before next X frame)
    (fun heap => exists returned after,
      tmr_task_fields_callback_return_facts fn self argument context before returned after /\
      timer_scan_continuation_valid sg (tmr_task_timers after)
        (tmr_task_scan_at_spoke spoke (tmr_task_timers after)) /\
      timer_scan_next_pointer sg (tmr_task_scan_at_spoke spoke (tmr_task_timers after)) =
        timer_id_pointer sg (nth spoke (tmr_task_timers after).(timerWheel) []) /\
      safeExec (eq after) (next returned) X /\
      TmrTaskFieldsRules.sepcon
        (tmr_task_current_fields_owned AppRep environment sg mask perr returned after) frame heap /\
      tmr_task_fields_callback_capability fn self argument heap).
Proof.
  intros Result fn self argument context before next X frame spoke Hspoke heap
    [returned [after [Hfacts [Hsafe [Howned Hcap]]]]].
  destruct (tmr_task_scan_at_spoke_valid sg spoke (tmr_task_timers after)
    Hspoke (proj1 (proj1 (proj2 Hfacts)))) as [Hscan Hpointer].
  exists returned, after; split; [exact Hfacts|]. split; [exact Hscan|].
  split; [exact Hpointer|]. split; [exact Hsafe|]. split; assumption.
Qed.

(** These consumers expose individual body obligations. They do not
    infer them from global validity or the callback type. The source and
    clear-field facts suffice for Fresh WITHOUT caller readiness. *)
Lemma tmr_task_fields_callback_return_boundary : forall fn self argument context before returned after,
  tmr_task_fields_callback_return_facts fn self argument context before returned after ->
  kernel_call_task_source context (fst before) ->
  kernel_call_stack_available context (fst before) ->
  (fst before).(SchedState).(isRunning) = true ->
  tmr_task_fields_caller_clear sg context (fst before) ->
  task_idle_ready sg (fst before).(TskState) ->
  kernel_call_task_source returned (fst after) /\
  kernel_call_stack_available returned (fst after) /\
  (fst after).(SchedState).(isRunning) = true /\
  tmr_task_fields_caller_clear sg returned (fst after) /\
  flag_active_fresh_registration returned returned (fst after) /\
  kernel_running_idle_ready sg (fst after).
Proof.
  intros fn self argument context before returned after
    [Hcall [Hready [Hservice [Hsame Hpreserves]]]] Hsource Havailable Hrunning Hclear Hidle.
  destruct Hpreserves as [Hsource' Havailable' Hrunning' Hclear' Hidle' Hpublic Hcurrent].
  specialize (Hsource' Hsource); specialize (Havailable' Havailable).
  specialize (Hrunning' Hrunning); specialize (Hclear' Hclear); specialize (Hidle' Hidle).
  split; [exact Hsource'|]. split; [exact Havailable'|]. split; [exact Hrunning'|].
  split; [exact Hclear'|]. split.
  - eapply tmr_task_fields_caller_clear_fresh; eassumption.
  - intro; exact Hidle'.
Qed.

(** This is a consequence of the callback's proved source postcondition.
    It is not obtained from the function-pointer type or a global heap rep. *)
Lemma tmr_task_fields_callback_return_current_consistency :
  forall fn self argument context before returned after,
  tmr_task_fields_callback_return_facts fn self argument context before returned after ->
  sched_current_consistency (fst before).(TskState) (fst before).(SchedState) ->
  sched_current_consistency (fst after).(TskState) (fst after).(SchedState).
Proof.
  intros fn self argument context before returned after
    [Hcall [Hready [Hservice [Hsame Hpreserves]]]] Hcurrent.
  eapply tmr_task_fields_callback_preserves_current_consistency; eassumption.
Qed.

(** Static owner registration is carried by same-call; it is not recreated
    by the callback and is not a field of its body contract. Only current
    public-slot ownership comes from the named source obligation above. *)
Lemma tmr_task_fields_callback_return_signal_input :
  forall critical fn self argument context before returned after eid observed,
  tmr_task_fields_callback_return_facts fn self argument context before returned after ->
  (tmr_task_timers before).(timerSignalSem) <> 0 ->
  (tmr_task_timers before).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  mutex_query_handle_protocol critical sg context.(os_sched_call_invocation) eid ->
  sem_query_public_slot (fst before) eid observed ->
  exists current,
    sem_pend_call_input critical sg returned.(os_sched_call_invocation)
      (tmr_task_timers after).(timerSignalSem) (fst after) eid current.
Proof.
  intros critical fn self argument context before returned after eid observed
    [Hcall [Hready [Hservice [Hsame Hpreserves]]]] Hnonnull Haddress Hid Hprotocol Hpublic.
  destruct Hpreserves as [Hsource Havailable Hrunning Hclear Hidle Hpublic_slot Hcache].
  destruct (Hpublic_slot eid observed Hnonnull Haddress Hpublic) as [current Hslot].
  exists current; eapply tmr_task_signal_input_after_service; eassumption.
Qed.

(** A current-ready receipt must be supplied at THIS SAME endpoint by its
    actual source producer. This conditional bridge is not a theorem that
    callbacks return ready, nor transport through the later Unlock call. *)
Lemma tmr_task_fields_callback_return_wait_at_ready_cut :
  forall critical fn self argument context before returned after eid observed,
  tmr_task_fields_callback_return_facts fn self argument context before returned after ->
  (tmr_task_timers before).(timerSignalSem) <> 0 ->
  (tmr_task_timers before).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  mutex_query_handle_protocol critical sg context.(os_sched_call_invocation) eid ->
  sem_query_public_slot (fst before) eid observed ->
  kernel_call_task_source context (fst before) ->
  kernel_call_stack_available context (fst before) ->
  (fst before).(SchedState).(isRunning) = true ->
  tmr_task_fields_caller_clear sg context (fst before) ->
  task_idle_ready sg (fst before).(TskState) ->
  os_sched_task_current_ready returned (fst after) -> event_table_layout_prop sg ->
  exists current, tmr_task_wait_instance environment critical sg returned after eid current.
Proof.
  intros critical fn self argument context before returned after eid observed Hfacts
    Hnonnull Haddress Hid Hprotocol Hpublic Hsource Havailable Hrunning Hclear Hidle Hready Hlayout.
  destruct (tmr_task_fields_callback_return_signal_input critical fn self argument
    context before returned after eid observed Hfacts Hnonnull Haddress Hid Hprotocol Hpublic)
    as [current Hinput].
  destruct (tmr_task_fields_callback_return_boundary fn self argument context before returned after
    Hfacts Hsource Havailable Hrunning Hclear Hidle)
    as [Hsource' [Havailable' [Hrunning' [Hclear' [Hfresh Hidle']]]]].
  exists current; apply tmr_task_wait_instance_task_boundary; try assumption.
  eapply tmr_task_fields_caller_clear_pend_stage; eassumption.
Qed.

(** NULL and ordered errors remain separate real returns. Neither bridge
    requires static owner registration, current-ready, Fresh, or Idle. *)
Lemma tmr_task_fields_callback_return_null_wait :
  forall critical fn self argument context before returned after eid observed,
  tmr_task_fields_callback_return_facts fn self argument context before returned after ->
  (tmr_task_timers before).(timerSignalSem) = 0 -> event_table_layout_prop sg ->
  tmr_task_wait_instance environment critical sg returned after eid observed.
Proof.
  intros critical fn self argument context before returned after eid observed
    [Hcall [Hready [Hservice [Hsame Hpreserves]]]] Hnull Hlayout.
  apply tmr_task_signal_null_wait; [|exact Hlayout].
  rewrite (tmr_task_signal_service_value _ _ Hservice); exact Hnull.
Qed.

Lemma tmr_task_fields_callback_return_error_wait :
  forall critical fn self argument context before returned after eid observed error,
  tmr_task_fields_callback_return_facts fn self argument context before returned after ->
  (tmr_task_timers after).(timerSignalSem) <> 0 ->
  (tmr_task_timers after).(timerSignalSem) = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot (fst after) eid observed ->
  sem_pend_precritical_error (tmr_task_timers after).(timerSignalSem)
    (event_slot_type_value (fst after).(EventState) eid)
    (fst after).(IntrState).(intNesting) (fst after).(IntrState).(lockNesting) = Some error ->
  event_table_layout_prop sg ->
  tmr_task_wait_instance environment critical sg returned after eid observed.
Proof.
  intros critical fn self argument context before returned after eid observed error Hfacts
    Hnonnull Haddress Hid Hpublic Herror Hlayout.
  eapply tmr_task_signal_error_wait; eassumption.
Qed.
End TaskFieldsCallbackContract.
