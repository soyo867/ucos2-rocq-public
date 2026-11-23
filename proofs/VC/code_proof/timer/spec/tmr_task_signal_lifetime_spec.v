Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_handle_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_protocol_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.sem.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

(** The service owns a NULL initialization result or one live semaphore.
    The existing handle protocol protects that object's incarnation from
    foreign registered clients. It does not grant another copy of its heap
    cells, promise a successful Pend, or constrain its count/waiter values. *)
Definition tmr_task_signal_lifetime (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (state : UCOS2_Verify_State) : Prop :=
  state.(TimerState).(timerSignalSem) = 0 \/
  exists eid node,
    state.(TimerState).(timerSignalSem) <> 0 /\
    state.(TimerState).(timerSignalSem) = event_addr sg eid /\
    valid_event_id sg eid /\ mutex_query_lookup state eid node /\
    node.(eventType) = OS_EVENT_TYPE_SEM /\
    mutex_query_handle_protocol critical sg invocation eid.

(** This relation describes one actual call's effect on the dedicated
    object. Generation equality excludes delete/recreate at the same
    address; type equality excludes replacing the semaphore by another
    kind of ECB. Other fields, objects, tasks and application data may change. *)
Definition tmr_task_signal_identity_preserved (sg : StableGlobVars)
  (before after : UCOS2_Verify_State) : Prop :=
  after.(TimerState).(timerSignalSem) = before.(TimerState).(timerSignalSem) /\
  forall eid previous,
    before.(TimerState).(timerSignalSem) <> 0 ->
    before.(TimerState).(timerSignalSem) = event_addr sg eid ->
    mutex_query_lookup before eid previous ->
    exists current, mutex_query_lookup after eid current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType).

Lemma tmr_task_signal_identity_preserved_refl : forall sg state,
  tmr_task_signal_identity_preserved sg state state.
Proof.
  intros sg state; split; [reflexivity|].
  intros eid previous Hnonnull Haddress Hlookup.
  exists previous; split; [exact Hlookup|]. split; reflexivity.
Qed.

Lemma tmr_task_signal_identity_preserved_trans : forall sg first middle last,
  tmr_task_signal_identity_preserved sg first middle ->
  tmr_task_signal_identity_preserved sg middle last ->
  tmr_task_signal_identity_preserved sg first last.
Proof.
  intros sg first middle last [Hfirst Hidentity] [Hlast Hidentity'].
  split; [congruence|]. intros eid previous Hnonnull Haddress Hlookup.
  destruct (Hidentity eid previous Hnonnull Haddress Hlookup)
    as [current [Hcurrent [Hgeneration Htype]]].
  destruct (Hidentity' eid current ltac:(rewrite Hfirst; exact Hnonnull)
    ltac:(rewrite Hfirst; exact Haddress) Hcurrent)
    as [final [Hfinal [Hgeneration' Htype']]].
  exists final; split; [exact Hfinal|]. split; congruence.
Qed.

Lemma tmr_task_signal_lifetime_preserved : forall critical sg invocation before after,
  tmr_task_signal_lifetime critical sg invocation before ->
  tmr_task_signal_identity_preserved sg before after ->
  tmr_task_signal_lifetime critical sg invocation after.
Proof.
  intros critical sg invocation before after Hlife [Hsignal Hidentity].
  destruct Hlife as [Hnull|[eid [previous
    [Hnonnull [Haddress [Hid [Hlookup [Htype Hprotocol]]]]]]]].
  - left; rewrite Hsignal; exact Hnull.
  - destruct (Hidentity eid previous Hnonnull Haddress Hlookup)
      as [current [Hcurrent [Hgeneration Hcurrent_type]]].
    right; exists eid, current.
    split; [rewrite Hsignal; exact Hnonnull|].
    split; [rewrite Hsignal; exact Haddress|]. split; [exact Hid|].
    split; [exact Hcurrent|]. split; [congruence|exact Hprotocol].
Qed.

Lemma tmr_task_signal_lifetime_same_call : forall critical sg original returned state,
  kernel_stack_call_same_call returned original ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) state ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) state.
Proof.
  intros critical sg original returned state Hsame Hlife.
  unfold tmr_task_signal_lifetime in *; rewrite (proj1 Hsame); exact Hlife.
Qed.

(** The NULL branch uses only an irrelevant logical witness. No ECB
    ownership or successful-creation premise is attached to that branch. *)
Lemma tmr_task_signal_lifetime_call_input : forall critical sg invocation state
  (fallback : OSEventAbstractState),
  tmr_task_signal_lifetime critical sg invocation state ->
  exists eid observed,
    sem_pend_call_input critical sg invocation state.(TimerState).(timerSignalSem)
      state eid observed.
Proof.
  intros critical sg invocation state fallback Hlife.
  destruct Hlife as [Hnull|[eid [node
    [Hnonnull [Haddress [Hid [Hlookup [Htype Hprotocol]]]]]]]].
  - exists 0, fallback; left; exact Hnull.
  - exists eid, node; right.
    split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
    split; [left; exact Hlookup|]. intros; exact Hprotocol.
Qed.

Lemma tmr_task_signal_lifetime_from_create_store :
  forall critical sg create_invocation service_invocation count before signal current timers,
  sem_create_api_program critical sg create_invocation count before signal current ->
  UCOS2_state_inv sg current ->
  timer_record_signal_result current.(TimerState) signal = Some timers ->
  (forall eid, signal = event_addr sg eid ->
    mutex_query_handle_protocol critical sg service_invocation eid) ->
  tmr_task_signal_lifetime critical sg service_invocation (replace_TimerS timers current).
Proof.
  intros critical sg create_invocation service_invocation count before signal current timers
    Hcreate Hvalid Hstore Hprotocol.
  pose proof (tmr_task_signal_recorded_value _ _ _ Hstore) as Hsignal.
  unfold tmr_task_signal_lifetime; cbn [replace_TimerS TimerState EventState].
  rewrite Hsignal.
  destruct (Z.eq_dec signal 0) as [Hnull|Hnonnull]; [left; exact Hnull|].
  destruct (tmr_task_signal_create_published_slot critical sg create_invocation count
    before signal current Hcreate Hnonnull) as [eid [node [Haddress [Hlookup Htype]]]].
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  pose proof (proj1 (event_pool_used_not_free sg current.(EventState) eid node
    Hpool Hlookup)) as Hid.
  right; exists eid, node.
  split; [exact Hnonnull|]. split; [exact Haddress|]. split; [exact Hid|].
  split; [exact Hlookup|]. split; [exact Htype|]. apply Hprotocol; exact Haddress.
Qed.

(** Timer-only writes retain the actual Event map. This consumer applies
    to each real advance/unlink/link/complete result once its signal-value
    equation has been proved from that operation. *)
Lemma tmr_task_timer_update_preserves_signal_identity : forall sg before timers,
  timers.(timerSignalSem) = before.(TimerState).(timerSignalSem) ->
  tmr_task_signal_identity_preserved sg before (replace_TimerS timers before).
Proof.
  intros sg before timers Hsignal; split; [exact Hsignal|].
  intros eid previous Hnonnull Haddress Hlookup.
  exists previous; split; [exact Hlookup|]. split; reflexivity.
Qed.

Lemma tmr_task_count_update_preserves_signal_identity : forall sg before selected node count,
  mutex_query_lookup before selected node ->
  tmr_task_signal_identity_preserved sg before (sem_count_update_state before selected node count).
Proof.
  intros sg before selected node count Hselected; split; [reflexivity|].
  intros eid previous Hnonnull Haddress Hlookup.
  eapply tmr_task_signal_count_update_preserves_identity; eassumption.
Qed.

(** This is the user-authorized application callback contract. It must
    be proved for the supplied callback program. The existing source-body
    capability still has to cover EVERY normal C outcome by that same
    program, so adding this premise cannot discard an actual bad outcome.
    It supplies no Task readiness, scheduler-return, or future-entry fact. *)
Definition tmr_task_callback_signal_lifetime {Application}
  (sg : StableGlobVars)
  (callback : (Z * Z * Z) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext) : Prop :=
  forall request original before returned after,
    callback request original before returned after ->
    tmr_task_signal_identity_preserved sg (fst before) (fst after).

Lemma tmr_task_fields_callback_return_signal_lifetime : forall Application critical sg
  (callback : (Z * Z * Z) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  fn self argument original before returned after,
  tmr_task_callback_signal_lifetime sg callback ->
  tmr_task_signal_lifetime critical sg original.(os_sched_call_invocation) (fst before) ->
  tmr_task_fields_callback_return_facts sg callback fn self argument original before returned after ->
  tmr_task_signal_lifetime critical sg returned.(os_sched_call_invocation) (fst after).
Proof.
  intros Application critical sg callback fn self argument original before returned after
    Hcallback Hlife [Hcall [Hready [Hservice [Hsame Hpreserves]]]].
  eapply tmr_task_signal_lifetime_same_call; [exact Hsame|].
  eapply tmr_task_signal_lifetime_preserved; [exact Hlife|].
  exact (Hcallback (fn, self, argument) original before returned after Hcall).
Qed.
