Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_call_entry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_link_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

(** The saved continuation predicate has the existing kernel assertion
    type; it is not silently reinterpreted as the callback product heap. *)
Definition TmrTaskLegacyAssertion := Assertion.
Definition tmr_task_kernel_any (_ : UCOS2_Verify_State) : Prop := True.
Definition tmr_task_legacy_any (_ : Z) (_ : UCOS2_Verify_State -> Prop) : Prop := True.

Definition tmr_task_kernel {Application} (world : tmr_task_scan_world Application) := fst world.
Definition tmr_task_application {Application} (world : tmr_task_scan_world Application) := snd world.

Definition tmr_task_link_raw_pre pointer base clock kind time delay period first entries frame :=
  TimerCalleeLift.lift_frame_contract
    (tmr_link_spec.tmr_link_raw_pre pointer base clock kind time delay period first entries) frame.
Definition tmr_task_link_raw_post pointer base clock kind time delay period first entries frame :=
  TimerCalleeLift.lift_frame_contract
    (tmr_link_spec.tmr_link_raw_post pointer base clock kind time delay period first entries) frame.

Definition tmr_task_pend_error_cell pointer := TmrTaskRules.lift (sem_pend_error_cell pointer).
Definition tmr_task_pend_capsules external platform environment saved_local context before :=
  TmrTaskRules.lift (sem_pend_optional_continuation_resources external platform environment
    saved_local context before).
Definition tmr_task_pend_post external platform environment critical saved_local sg context
  mask signal ticks pointer before X :=
  TmrTaskRules.lift (sem_pend_continuation_call_post external platform environment critical
    saved_local sg context mask signal ticks pointer before X).

Module TmrTaskAnnotationOld.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.
Definition pend_pre external platform environment critical saved_local sg context
  mask signal ticks pointer before eid observed X : Assertion :=
  coq_prop (sem_pend_runtime_nonblocking critical sg context environment signal before eid /\
    sem_pend_observed_admission environment critical sg context signal before eid /\
    sem_pend_profile sg /\ kernel_tcb_stack_field_layout sg /\
    sem_pend_call_input critical sg context.(os_sched_call_invocation) signal before eid observed /\
    safeExec (LastSeen before)
      (StateRelMonad.bind (atomic_cmd (sem_pend_runtime_program external platform environment
        critical sg context signal ticks)) sem_query_observe_error) X) &&
  mutex_query_closed platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask before **
  os_sched_context_resources external context ** unmap_table_rep sg **
  sem_pend_error_cell pointer **
  sem_pend_optional_continuation_resources external platform environment saved_local context before.
End TmrTaskAnnotationOld.
Definition tmr_task_pend_call_pre external platform environment critical saved_local sg context
  mask signal ticks pointer before eid observed X :=
  TmrTaskRules.lift (TmrTaskAnnotationOld.pend_pre external platform environment critical
    saved_local sg context mask signal ticks pointer before eid observed X).

Definition tmr_task_profile sg : Prop :=
  valid_stable_glob_vars sg /\ tmr_link_layout /\ tmr_link_profile sg /\
  tmr_unlink_layout /\ tmr_unlink_profile sg /\ sem_pend_profile sg /\
  kernel_tcb_stack_field_layout sg.

Definition tmr_task_global_addresses sg signal wheel time current running ints locks high
  priority high_tcb table counter unmap group rows : Prop :=
  signal = sg.(g_OSTmrSemSignal) /\ wheel = sg.(g_OSTmrWheelTbl) /\
  time = sg.(g_OSTmrTime) /\ current = sg.(g_OSTCBCur) /\
  os_sched_lock_global_addresses sg running ints locks /\
  os_sched_unlock_global_addresses sg running ints locks high priority high_tcb table
    counter unmap group rows.

Lemma tmr_task_link_raw_pre_slice : forall pointer base clock kind time delay period first
  entries frame environment heap,
  TmrTaskRules.slice environment
    (tmr_task_link_raw_pre pointer base clock kind time delay period first entries frame) heap <->
  tmr_link_spec.tmr_link_raw_pre pointer base clock kind time delay period first entries
    (TmrTaskRules.slice environment frame) heap.
Proof. intros; reflexivity. Qed.
Lemma tmr_task_link_raw_post_slice : forall pointer base clock kind time delay period first
  entries frame environment heap,
  TmrTaskRules.slice environment
    (tmr_task_link_raw_post pointer base clock kind time delay period first entries frame) heap <->
  tmr_link_spec.tmr_link_raw_post pointer base clock kind time delay period first entries
    (TmrTaskRules.slice environment frame) heap.
Proof. intros; reflexivity. Qed.

Inductive TmrTaskCellKind := TaskByteCell | TaskUIntCell | TaskPointerCell.
Inductive TmrTaskImageField := TaskNextField | TaskMatchField | TaskOptionField |
  TaskCallbackField | TaskArgumentField | TaskStateField.

Definition tmr_task_cell (kind : TmrTaskCellKind) (address value : Z) : TmrTaskRules.expr :=
  match kind with
  | TaskByteCell => TmrTaskRules.store_uchar address value
  | TaskUIntCell => TmrTaskRules.store_uint address value
  | TaskPointerCell => TmrTaskRules.store_ptr address value
  end.

Definition tmr_task_image_value (field : TmrTaskImageField) (image : TimerImage) : Z :=
  match field with
  | TaskNextField => image.(timerImageNext)
  | TaskMatchField => image.(timerImageMatch)
  | TaskOptionField => image.(timerImageOption)
  | TaskCallbackField => image.(timerImageCallback)
  | TaskArgumentField => image.(timerImageArg)
  | TaskStateField => image.(timerImageState)
  end.

Definition tmr_task_image_read {Application} (world : tmr_task_scan_world Application)
  index field value : Prop := exists image,
  (tmr_task_timers world).(timerImages) index = Some image /\
  value = tmr_task_image_value field image.

Definition tmr_task_head (sg : StableGlobVars) (spoke : nat) (timers : GlobTimerState) : Z :=
  timer_id_pointer sg (nth spoke timers.(timerWheel) []).

Definition tmr_task_spoke_index (sg : StableGlobVars) (timers : GlobTimerState) : nat :=
  Z.to_nat (timer_spoke sg.(osKernelConfig) timers.(timerTime)).

Definition tmr_task_unlink_world {Application} sg
  (before : tmr_task_scan_world Application) index (after : tmr_task_scan_world Application) :=
  exists timers, timer_unlink sg (tmr_task_timers before) index = Some timers /\
    after = tmr_task_set_timers timers before.
Definition tmr_task_link_world {Application} sg
  (before : tmr_task_scan_world Application) index (after : tmr_task_scan_world Application) :=
  exists timers, timer_link sg (tmr_task_timers before) index true = Some timers /\
    after = tmr_task_set_timers timers before.
Definition tmr_task_complete_world {Application}
  (before : tmr_task_scan_world Application) index (after : tmr_task_scan_world Application) :=
  exists timers, timer_complete (tmr_task_timers before) index = Some timers /\
    after = tmr_task_set_timers timers before.

(** This is the actual dispatch domain of the callback, not every arbitrary
    ready timer world.  In particular the callback's self/argument come from
    an allocated timer image selected by expiration dispatch.  No condition
    mentions preservation of the old next pointer or old scan suffix. *)
Definition tmr_task_callback_dispatch_domain {Application} sg fn self argument
  (world : tmr_task_scan_world Application) : Prop :=
  exists prior index cached dispatched,
    valid_timer_state sg (tmr_task_timers prior) /\
    timer_expire_dispatch sg (tmr_task_timers prior) index =
      Some (cached, Some (fn, self, argument), dispatched) /\
    world = tmr_task_set_timers dispatched prior.

Definition tmr_task_dispatch_prepared {Application} sg
  (before : tmr_task_scan_world Application) index cached
  (after : tmr_task_scan_world Application) : Prop :=
  exists request dispatched,
    timer_expire_dispatch sg (tmr_task_timers before) index = Some (cached, request, dispatched) /\
    after = tmr_task_set_timers dispatched before.

Definition tmr_task_pend_return {Application} external platform environment critical sg
  (effects : TmrTaskEffects Application) context signal before error returned after : Prop :=
  tmr_task_pend_program external platform environment critical sg effects context signal
    before (error, returned) after.
Definition tmr_task_lock_return {Application} critical sg
  (effects : TmrTaskEffects Application) context before after : Prop :=
  tmr_task_lock_program critical sg effects context before tt after.
Definition tmr_task_unlock_return {Application} external critical sg
  (effects : TmrTaskEffects Application) context before returned after : Prop :=
  tmr_task_unlock_program external critical sg effects context before returned after.
Definition tmr_task_callback_return {Application}
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  fn self argument context before returned after : Prop :=
  callback (fn, self, argument) context before returned after.

Section CallbackDispatchContract.
Context {Application : Type} (AppRep : Application -> TmrTaskRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> TmrTaskLegacyAssertion) (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext) (mask perr : Z).

Definition tmr_task_callback_dispatch_pre fn self argument context world arguments :=
  TmrTaskRules.andp
    (TmrTaskRules.coq_prop (tmr_task_callback_dispatch_domain sg fn self argument world))
    (tmr_task_callback_pre AppRep external platform environment critical saved_local sg
      mask perr self argument context world arguments).

Definition tmr_task_callback_dispatch_specification fn self argument
  : TmrTaskCallback.Spec TmrTaskCallback.timer_callback_signature :=
  fun body => @TmrTaskRules.allp OsSchedCallContext (fun context =>
    @TmrTaskRules.allp (tmr_task_scan_world Application) (fun world =>
      TmrTaskCallback.HoareFun TmrTaskCallback.timer_callback_signature
        (tmr_task_callback_dispatch_pre fn self argument context world)
        (tmr_task_callback_post AppRep external platform environment critical saved_local sg
          callback mask perr fn self argument context world) body)).

Definition tmr_task_callback_dispatch_capability fn self argument :=
  @TmrTaskCallback.func_ptr_spec TmrTaskCallback.timer_callback_signature fn
    (tmr_task_callback_dispatch_specification fn self argument).

Lemma tmr_task_callback_dispatch_specification_environment_only : forall fn self argument,
  TmrTaskCallback.specification_environment_only
    (tmr_task_callback_dispatch_specification fn self argument).
Proof.
  intros fn self argument; apply TmrTaskCallback.allp_specification_environment_only.
  intro context; apply TmrTaskCallback.allp_specification_environment_only.
  intro entry_state; apply TmrTaskCallback.HoareFun_specification_environment_only.
Qed.

Lemma tmr_task_callback_dispatch_capability_from_source : forall fn self argument
  (functions : TmrTaskCallback.callback_environment)
  (body : TmrTaskCallback.FunSem TmrTaskCallback.timer_callback_signature),
  fn <> 0 ->
  TmrTaskCallback.source_functions functions TmrTaskCallback.timer_callback_signature fn = Some body ->
  (forall context world,
    TmrTaskCallback.callback_source_evidence functions
      TmrTaskCallback.timer_callback_signature body
      (tmr_task_callback_dispatch_pre fn self argument context world)
      (tmr_task_callback_post AppRep external platform environment critical saved_local sg
        callback mask perr fn self argument context world)) ->
  forall heap, tmr_task_callback_dispatch_capability fn self argument (heap, functions).
Proof.
  intros fn self argument functions body Hnonnull Hlookup Hevidence heap.
  split; [exact Hnonnull|]. exists body; split; [exact Hlookup|].
  intros context world; exact (Hevidence context world).
Qed.
End CallbackDispatchContract.

Record TmrTaskScanHistory (Application : Type) : Type := {
  tmr_task_history_before : tmr_task_scan_world Application;
  tmr_task_history_context : OsSchedCallContext;
  tmr_task_history_completed : list TmrTaskIterationObservation;
  tmr_task_history_error : Z;
  tmr_task_history_waited : tmr_task_scan_world Application;
  tmr_task_history_wait_context : OsSchedCallContext;
  tmr_task_history_locked : tmr_task_scan_world Application
}.
Arguments tmr_task_history_before {Application} _.
Arguments tmr_task_history_context {Application} _.
Arguments tmr_task_history_completed {Application} _.
Arguments tmr_task_history_error {Application} _.
Arguments tmr_task_history_waited {Application} _.
Arguments tmr_task_history_wait_context {Application} _.
Arguments tmr_task_history_locked {Application} _.

Definition tmr_task_history_start {Application} (history : TmrTaskScanHistory Application) :=
  tmr_task_set_timers (timer_service_advance (tmr_task_timers history.(tmr_task_history_locked)))
    history.(tmr_task_history_locked).
Definition tmr_task_history_spoke {Application} sg (history : TmrTaskScanHistory Application) :=
  tmr_task_spoke_index sg (tmr_task_timers (tmr_task_history_start history)).
Definition tmr_task_history_scan {Application} sg (history : TmrTaskScanHistory Application) :=
  timer_scan_begin sg (tmr_task_timers (tmr_task_history_start history)).

Section AnnotationPredicates.
Context {Application : Type} (AppRep : Application -> TmrTaskRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (effects : TmrTaskEffects Application) (mask : Z).

Definition tmr_task_base_owned context (world : tmr_task_scan_world Application)
  : TmrTaskRules.expr :=
  TmrTaskRules.sepcon (tmr_task_context_rep external platform critical sg mask context (fst world))
    (TmrTaskRules.sepcon
      (TmrTaskRules.lift (sem_pend_optional_continuation_resources external platform
        (Some environment) saved_local context (fst world))) (AppRep (snd world))).

(** A residual lens, not an assumed field ownership.  Each C which-implies
    must prove extraction of its actual cell and this wand from the old
    resources.  A store uses the NEW value/world in the wand; a read uses
    the original one.  This makes missing split/update/merge facts targets. *)
Definition tmr_task_cell_rest perr kind address value context
  (world : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.wand (tmr_task_cell kind address value)
    (tmr_task_owned AppRep external platform environment critical saved_local sg
      mask perr context world).

Definition tmr_task_two_cell_rest perr kind1 address1 value1 kind2 address2 value2 context
  (world : tmr_task_scan_world Application) : TmrTaskRules.expr :=
  TmrTaskRules.wand
    (TmrTaskRules.sepcon (tmr_task_cell kind1 address1 value1)
      (tmr_task_cell kind2 address2 value2))
    (tmr_task_owned AppRep external platform environment critical saved_local sg
      mask perr context world).

(** Source callees keep their raw footprint.  These restoration predicates
    are entailments to be ESTABLISHED by split/update/merge at the caller;
    they do not add behavior or a postcondition to either callee. *)
Definition tmr_task_unlink_restores perr pointer base match_time next previous first entries
  frame context (after : tmr_task_scan_world Application) : Prop :=
  TmrTaskRules.derivable1
    (TimerCalleeLift.tmr_unlink_raw_post pointer base match_time next previous first entries frame)
    (tmr_task_owned AppRep external platform environment critical saved_local sg mask perr context after).
Definition tmr_task_link_restores perr pointer base clock kind time delay period first entries
  frame context (after : tmr_task_scan_world Application) : Prop :=
  TmrTaskRules.derivable1
    (tmr_task_link_raw_post pointer base clock kind time delay period first entries frame)
    (tmr_task_owned AppRep external platform environment critical saved_local sg mask perr context after).

Definition tmr_task_wait_instance context (world : tmr_task_scan_world Application) eid observed : Prop :=
    sem_pend_call_input critical sg context.(os_sched_call_invocation)
      (tmr_task_timers world).(timerSignalSem) (fst world) eid observed /\
    sem_pend_runtime_nonblocking critical sg context (Some environment)
      (tmr_task_timers world).(timerSignalSem) (fst world) eid /\
    sem_pend_observed_admission (Some environment) critical sg context
      (tmr_task_timers world).(timerSignalSem) (fst world) eid /\
    sem_pend_observed_blocking_layout (Some environment) critical sg context
      (fst world) eid sg.(g_OSTCBCur) sg.(g_OSRdyGrp) sg.(g_OSRdyTbl).

Definition tmr_task_wait_input context (world : tmr_task_scan_world Application) : Prop :=
  exists eid observed, tmr_task_wait_instance context world eid observed.

Definition tmr_task_loop_continuation context completed (world : tmr_task_scan_world Application)
  (X : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    tmr_task_scan_world Application -> Prop) : Prop :=
  forall count, safeExec (eq world)
    (StateRelMonad.bind
      (tmr_task_loop_prefix_program external platform environment critical sg effects count context)
      (fun tail => StateRelMonad.ret (completed ++ fst tail, snd tail))) X.

Definition tmr_task_outer_facts original_context original context completed world X : Prop :=
  tmr_task_loop_prefix external platform environment critical sg effects original
    original_context completed world context /\
  tmr_task_loop_continuation context completed world X.

Definition tmr_task_scan_history original_context original
  (history : TmrTaskScanHistory Application) : Prop :=
  tmr_task_loop_prefix external platform environment critical sg effects original
    original_context history.(tmr_task_history_completed) history.(tmr_task_history_before)
    history.(tmr_task_history_context) /\
  tmr_task_pend_program external platform environment critical sg effects
    history.(tmr_task_history_context)
    (tmr_task_timers history.(tmr_task_history_before)).(timerSignalSem)
    history.(tmr_task_history_before)
    (history.(tmr_task_history_error), history.(tmr_task_history_wait_context))
    history.(tmr_task_history_waited) /\
  tmr_task_lock_program critical sg effects history.(tmr_task_history_wait_context)
    history.(tmr_task_history_waited) tt history.(tmr_task_history_locked).

Definition tmr_task_scan_continuation context completed error visited spoke scan
  (world : tmr_task_scan_world Application)
  (X : (list TmrTaskIterationObservation * OsSchedCallContext) ->
    tmr_task_scan_world Application -> Prop) : Prop :=
  forall count, safeExec (eq world)
    (StateRelMonad.bind (tmr_task_scan_program sg (tmr_task_callback_program effects)
      spoke context scan) (fun tail =>
    StateRelMonad.bind (tmr_task_unlock_program external critical sg effects (snd tail))
      (fun returned =>
    StateRelMonad.bind
      (tmr_task_loop_prefix_program external platform environment critical sg effects count returned)
      (fun later => StateRelMonad.ret
        (completed ++ {| tmr_task_wait_error := error;
                         tmr_task_iteration_events := visited ++ fst tail;
                         tmr_task_iteration_context := returned |} :: fst later,
         snd later))))) X.

Definition tmr_task_scan_facts original_context original history visited context world scan X : Prop :=
  tmr_task_scan_history original_context original history /\
  tmr_task_scan_prefix sg (tmr_task_callback_program effects) (tmr_task_history_spoke sg history)
    (tmr_task_history_start history) history.(tmr_task_history_wait_context)
    (tmr_task_history_scan sg history) visited world context scan /\
  timer_scan_continuation_valid sg (tmr_task_timers world) scan /\
  tmr_task_spoke_in_range sg (tmr_task_history_spoke sg history) /\
  tmr_task_scan_call_ready external critical sg context world /\
  tmr_task_service_frame (tmr_task_timers (tmr_task_history_start history)) (tmr_task_timers world) /\
  tmr_task_scan_continuation context history.(tmr_task_history_completed)
    history.(tmr_task_history_error) visited (tmr_task_history_spoke sg history) scan world X.
End AnnotationPredicates.
