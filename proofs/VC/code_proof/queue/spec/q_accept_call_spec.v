Require Export Ucos2Verify.VC.code.queue.spec.q_accept_spec.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.VC.code.queue.spec.q_query_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import UCOS2_C_Rules ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Public source-call layer. The existing q_accept_critical operation is
    unchanged; it runs on the freshly acquired state, not the caller's old
    observation. A successful NULL message is distinct from Q_EMPTY. *)
Definition q_accept_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    q_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 2 ->
      mutex_query_handle_protocol critical sg invocation eid)).

Definition q_accept_acquire_facts := q_query_acquire_facts.

Definition q_accept_save_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Assertion :=
  coq_prop (mutex_query_handle_protocol critical sg invocation eid /\
    mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q) &&
  (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg before).

Definition q_accept_finished (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry after : UCOS2_Verify_State) (observed current : OSEventAbstractState)
  (message : addr) (error : OSErrCode) : Prop :=
  q_accept_acquire_facts critical sg invocation eid mask saved before entry observed current /\
  q_accept_critical sg eid entry (message, error) after.

(** The acquisition token keeps entry as its index. Restore consumes the
    updated full invariant; no arbitrary inside-token reindexing is assumed. *)
Definition q_accept_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry after : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) (message : addr) (error : OSErrCode) : Assertion :=
  coq_prop (q_accept_finished critical sg invocation eid mask saved before entry after observed current message error) &&
  (critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_inv sg after).

Definition q_accept_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry after : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) (message : addr) (error : OSErrCode) : Assertion :=
  coq_prop (q_accept_finished critical sg invocation eid mask saved before entry after observed current message error) &&
  mutex_query_closed platform critical sg invocation origin mask after.

Lemma q_accept_restore_consequence : forall platform critical sg invocation origin
  eid mask saved before entry after observed current message error,
  q_accept_finished critical sg invocation eid mask saved before entry after observed current message error ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation after |--
  mutex_query_closed platform critical sg invocation origin mask after.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry after observed current message error
    [Hfacts Hstep].
  destruct Hfacts as [_ [Hvalid [[Hsaved Hmask] [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof (q_accept_critical_preserves_validity sg entry eid current (message, error) after Hvalid Hlookup Htype Hstep) as Hafter.
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.

Definition q_accept_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  : program UCOS2_Verify_State (addr * OSErrCode) :=
  fun before result after =>
    (pe = 0 /\ result = (0, OS_ERR_PEVENT_NULL) /\ after = before) \/
    (pe <> 0 /\ exists eid observed,
      pe = event_addr sg eid /\ valid_event_id sg eid /\ q_query_public_slot before eid observed /\
      ((event_slot_type_value before.(EventState) eid <> 2 /\ result = (0, OS_ERR_EVENT_TYPE) /\ after = before) \/
       (mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q /\
        exists entry current,
          critical_region_interval critical sg invocation before entry /\ mutex_query_lookup entry eid current /\
          current.(eventType) = OS_EVENT_TYPE_Q /\ current.(eventGeneration) = observed.(eventGeneration) /\
          q_accept_critical sg eid entry result after))).

Definition q_accept_observe_message (result : addr * OSErrCode)
  : program (UCOS2_Verify_State -> Prop) addr := StateRelMonad.ret (fst result).

Lemma q_accept_call_null : forall critical sg invocation before,
  q_accept_call_program critical sg invocation 0 before (0, OS_ERR_PEVENT_NULL) before.
Proof. intros; left; auto. Qed.

Lemma q_accept_call_wrong_type : forall critical sg invocation pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  q_query_public_slot before eid observed -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_accept_call_program critical sg invocation pe before (0, OS_ERR_EVENT_TYPE) before.
Proof.
  intros critical sg invocation pe before eid observed Hpe Haddr Hid Hslot Htype.
  right; split; [exact Hpe|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|]; left; auto.
Qed.

Lemma q_accept_call_endpoint : forall critical sg invocation pe before eid observed mask saved
  entry after current message error,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  q_accept_finished critical sg invocation eid mask saved before entry after observed current message error ->
  q_accept_call_program critical sg invocation pe before (message, error) after.
Proof.
  intros critical sg invocation pe before eid observed mask saved entry after current message error Hpe Haddr Hid
    [[Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]] Hstep].
  right; split; [exact Hpe|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [left; exact Hbefore|].
  right; split; [exact Hbefore|]; split; [exact Htype|]; exists entry, current.
  split; [exact Hinterval|]; split; [exact Hlookup|]; split; [exact Hcurrent|]; split; assumption.
Qed.

Lemma q_accept_call_safe_return : forall critical sg invocation pe before after message error X,
  q_accept_call_program critical sg invocation pe before (message, error) after ->
  safeExec (LastSeen before) (bind (atomic_cmd (q_accept_call_program critical sg invocation pe)) q_accept_observe_message) X ->
  safeExec (LastSeen after) (StateRelMonad.ret message) X.
Proof.
  intros critical sg invocation pe before after message error X Hsem Hsafe.
  assert (Hatomic : hs_eval (atomic_cmd (q_accept_call_program critical sg invocation pe))
    (LastSeen before) (LastSeen after) (message, error)).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P HP.
    exists (RTrans_Abs after); split.
    - exists before, after; split; [apply HP; exact I|].
      split; [exact Hsem|intro state; split; trivial].
    - intro state; split; trivial. }
  exact (highstepbind_derive _ _ _ (message, error) (LastSeen after) Hatomic X Hsafe).
Qed.
