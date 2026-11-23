Require Export Ucos2Verify.VC.code.queue.spec.q_accept_annotation_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_proof_helpers.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Both a successful dequeue and Q_EMPTY execute Restore.  NULL/type errors
    return before Save.  The result observes the error as well as the message,
    so an empty queue is not confused with a successful NULL message. *)
Definition q_accept_uses_restore (error : OSErrCode) : bool :=
  match error with OS_ERR_NONE | OS_ERR_Q_EMPTY => true | _ => false end.

Definition q_accept_api_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  : program UCOS2_Verify_State (OSErrCode * addr) :=
  bind (q_accept_call_program critical sg invocation pe)
    (fun result => if q_accept_uses_restore (snd result) then
      bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret (snd result, fst result))
      else StateRelMonad.ret (snd result, fst result)).

Definition q_accept_api_safe critical sg invocation pe before
  (X : OSErrCode * addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (q_accept_api_program critical sg invocation pe) X.

Definition q_accept_return_safe (current : UCOS2_Verify_State)
  (message : addr) (error : OSErrCode)
  (X : OSErrCode * addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret (error, message)) X.

Definition q_accept_api_post critical sg invocation pe before message error current : Prop :=
  q_accept_api_program critical sg invocation pe before (error, message) current.

Lemma q_accept_api_program_iff : forall critical sg invocation pe before message error current,
  q_accept_api_program critical sg invocation pe before (error, message) current <->
  exists released,
    q_accept_call_program critical sg invocation pe before (message, error) released /\
    (if q_accept_uses_restore error then
       critical_region_interval critical sg invocation released current
     else current = released).
Proof.
  intros; unfold q_accept_api_program, StateRelMonad.bind, update, StateRelMonad.ret.
  split.
  - intros [[value code] [released [Hcall Hreturn]]]; cbn in Hreturn.
    destruct (q_accept_uses_restore code) eqn:Hcode.
    + destruct Hreturn as [[] [after [Hinterval [Hresult Hafter]]]].
      injection Hresult as Herror Hmessage; subst code value current.
      exists released; rewrite Hcode; auto.
    + destruct Hreturn as [Hresult Hafter].
      injection Hresult as Herror Hmessage; subst code value current.
      exists released; rewrite Hcode; auto.
  - intros [released [Hcall Hreturn]].
    exists (message, error), released; split; [exact Hcall|]; cbn.
    destruct (q_accept_uses_restore error).
    + exists tt, current; split; [exact Hreturn|split; reflexivity].
    + split; [reflexivity|symmetry; exact Hreturn].
Qed.

Lemma q_accept_api_early_return : forall critical sg invocation pe before message error current,
  q_accept_uses_restore error = false ->
  q_accept_call_program critical sg invocation pe before (message, error) current ->
  q_accept_api_program critical sg invocation pe before (error, message) current.
Proof.
  intros; apply q_accept_api_program_iff; exists current; split; [assumption|].
  rewrite H; reflexivity.
Qed.

Lemma q_accept_api_restored_return : forall critical sg invocation pe before message error released current,
  q_accept_uses_restore error = true ->
  q_accept_call_program critical sg invocation pe before (message, error) released ->
  critical_region_interval critical sg invocation released current ->
  q_accept_api_program critical sg invocation pe before (error, message) current.
Proof.
  intros; apply q_accept_api_program_iff; exists released; split; [assumption|].
  rewrite H; assumption.
Qed.

Lemma q_accept_critical_uses_restore : forall sg eid entry message error released,
  q_accept_critical sg eid entry (message, error) released ->
  q_accept_uses_restore error = true.
Proof.
  intros sg eid entry message error released [node [q [_ [_ Hstep]]]].
  destruct (Z.ltb 0 (queue_entries q)).
  - destruct Hstep as [value [next [slots [_ [_ [Hresult _]]]]]].
    injection Hresult as Hmessage Herror; subst error; reflexivity.
  - destruct Hstep as [Hresult _].
    injection Hresult as Hmessage Herror; subst error; reflexivity.
Qed.

(** The storage-binding premise is supplied by the existing Queue resource
    representation, not added to the public input domain.  Empty registered
    intervals give a normal endpoint; no fairness/termination claim follows. *)
Lemma q_accept_api_program_has_result : forall critical sg invocation pe before eid observed,
  UCOS2_state_inv sg before -> queue_published_storage_binding before.(EventState) ->
  q_accept_call_input critical sg invocation pe before eid observed ->
  exists error message current,
    q_accept_api_program critical sg invocation pe before (error, message) current.
Proof.
  intros critical sg invocation pe before eid observed Hvalid Hbinding Hinput.
  destruct Hinput as [Hzero|[Hnonzero [Haddr [Hid [Hslot Hprotocol]]]]].
  - subst pe; exists OS_ERR_PEVENT_NULL, 0, before.
    apply q_accept_api_early_return; [reflexivity|apply q_accept_call_null].
  - destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 2) as [Htype|Htype].
    + destruct (q_query_public_slot_is_queue before eid observed Hslot Htype) as [Hlookup Hqueue].
      destruct (q_query_current_fields sg before eid observed Hvalid Hlookup Hqueue) as [q [Hq Hqvalid]].
      destruct (q_accept_critical_exists sg before eid observed q Hlookup Hq Hbinding)
        as [[message error] [released Hstep]].
      assert (Hsaved : interrupt_saved_value 0 0).
      { unfold interrupt_saved_value, valid_os_cpu_sr, armv7a_irq_fiq_mask; cbn; lia. }
      assert (Hfacts : q_accept_acquire_facts critical sg invocation eid 0 0
        before before observed observed).
      { unfold q_accept_acquire_facts, q_query_acquire_facts.
        split; [constructor|]; split; [exact Hvalid|]; split; [exact Hsaved|].
        repeat split; assumption || reflexivity. }
      exists error, message, released.
      eapply q_accept_api_restored_return; [eapply q_accept_critical_uses_restore; exact Hstep| |constructor].
      eapply (q_accept_call_endpoint critical sg invocation pe before eid observed 0 0
        before released observed message error); try eassumption.
      split; assumption.
    + exists OS_ERR_EVENT_TYPE, 0, before; apply q_accept_api_early_return; [reflexivity|].
      exact (q_accept_call_wrong_type critical sg invocation pe before eid observed
        Hnonzero Haddr Hid Hslot Htype).
Qed.

Lemma q_accept_api_safe_return : forall critical sg invocation pe before message error current X,
  q_accept_api_program critical sg invocation pe before (error, message) current ->
  q_accept_api_safe critical sg invocation pe before X ->
  q_accept_return_safe current message error X.
Proof.
  intros critical sg invocation pe before message error current X Hprogram Hsafe.
  unfold q_accept_api_safe in Hsafe; unfold q_accept_return_safe.
  eapply (highstependret_derive (q_accept_api_program critical sg invocation pe)
    (eq before) (error, message) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; auto.
Qed.

Lemma q_accept_save_pre_closed : forall platform critical sg invocation origin mask before eid observed,
  q_accept_save_pre platform critical sg invocation origin mask before eid observed --||--
  coq_prop (mutex_query_handle_protocol critical sg invocation eid /\
    mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q) &&
  mutex_query_closed platform critical sg invocation origin mask before.
Proof. intros; rewrite mutex_query_closed_equiv; reflexivity. Qed.

(** The actual return world indexes both the interval and the very same closed
    heap.  The old checkpoint-only post is retained for historical consumers;
    the current C declaration consumes this additive return interface. *)
Definition q_accept_api_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry released : UCOS2_Verify_State)
  (eid : EventID) (observed focused : OSEventAbstractState) (message : addr) (error : OSErrCode) : Assertion :=
  EX current,
    coq_prop (q_accept_finished critical sg invocation eid mask saved before entry released observed focused message error /\
      critical_region_interval critical sg invocation released current) &&
    mutex_query_closed platform critical sg invocation origin mask current.

Lemma q_accept_restore_return_consequence :
  forall platform critical sg invocation origin eid mask saved before entry released current observed focused message error,
  q_accept_finished critical sg invocation eid mask saved before entry released observed focused message error ->
  critical_region_interval critical sg invocation released current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation current |--
  q_accept_api_restore_post platform critical sg invocation origin mask saved
    before entry released eid observed focused message error.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry released current observed focused message error
    Hfinished Hinterval.
  pose proof Hfinished as [Hfacts Hstep].
  pose proof Hfacts as [_ [Hentry [[Hsaved Hmask] [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof (q_accept_critical_preserves_validity sg entry eid focused (message, error) released
    Hentry Hlookup Htype Hstep) as Hreleased.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation released current Hinterval Hreleased)) as Hcurrent.
  unfold q_accept_api_restore_post; Exists current; rewrite Hmask.
  unfold mutex_query_closed; entailer!.
Qed.

Lemma q_accept_restore_immediate_consequence :
  forall platform critical sg invocation origin eid mask saved before entry released observed focused message error,
  q_accept_finished critical sg invocation eid mask saved before entry released observed focused message error ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation released |--
  q_accept_api_restore_post platform critical sg invocation origin mask saved
    before entry released eid observed focused message error.
Proof.
  intros; eapply q_accept_restore_return_consequence; [exact H|constructor].
Qed.
