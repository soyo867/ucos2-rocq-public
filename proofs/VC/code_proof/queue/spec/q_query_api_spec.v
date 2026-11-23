Require Export Ucos2Verify.VC.code.queue.spec.q_query_annotation_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_query_proof_helpers.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The source first rejects NULL arguments and reads the unmasked Event
    discriminator.  The successful arm obtains a fresh protected state,
    copies all five OS_Q_DATA components, and then returns through Restore.
    The output snapshot belongs to the protected state, not to the possibly
    changed state at return.  No lifetime or validity condition is inserted
    into this program: the existing public admission proves those facts. *)
Definition q_query_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (pe pd : addr)
  : program UCOS2_Verify_State (Z * option QueueQuerySnapshot) :=
  if Z.eqb pe 0 then StateRelMonad.ret (4, None)
  else if Z.eqb pd 0 then StateRelMonad.ret (9, None)
  else StateRelMonad.bind (get' (fun s => s)) (fun before =>
    if Z.eqb (event_slot_type_value before.(EventState) eid) 2 then
      StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.bind (q_query_critical sg eid) (fun snapshot =>
          StateRelMonad.bind (update (critical_region_interval critical sg invocation))
            (fun _ => StateRelMonad.ret (0, Some snapshot))))
    else StateRelMonad.ret (1, None)).

Definition q_query_safe critical sg invocation eid pe pd before
  (X : Z -> option QueueQuerySnapshot -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (q_query_program critical sg invocation eid pe pd)
    (fun result current => X (fst result) (snd result) current).

Lemma q_query_program_null_event : forall critical sg invocation eid pd before,
  q_query_program critical sg invocation eid 0 pd before (4, None) before.
Proof. intros; unfold q_query_program, StateRelMonad.ret; cbn; auto. Qed.

Lemma q_query_program_null_output : forall critical sg invocation eid pe before,
  pe <> 0 -> q_query_program critical sg invocation eid pe 0 before (9, None) before.
Proof.
  intros; unfold q_query_program; rewrite (proj2 (Z.eqb_neq _ _) H).
  unfold StateRelMonad.ret; cbn; auto.
Qed.

Lemma q_query_program_wrong_type : forall critical sg invocation eid pe pd before,
  pe <> 0 -> pd <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_query_program critical sg invocation eid pe pd before (1, None) before.
Proof.
  intros critical sg invocation eid pe pd before Hpe Hpd Htype.
  unfold q_query_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe),
    (proj2 (Z.eqb_neq _ _) Hpd).
  unfold StateRelMonad.bind, get', get.
  exists before, before; split; [split; reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) Htype); split; reflexivity.
Qed.

Lemma q_query_program_success :
  forall critical sg invocation eid pe pd before entry current snapshot,
  pe <> 0 -> pd <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  critical_region_interval critical sg invocation before entry ->
  q_query_critical sg eid entry snapshot entry ->
  critical_region_interval critical sg invocation entry current ->
  q_query_program critical sg invocation eid pe pd before (0, Some snapshot) current.
Proof.
  intros critical sg invocation eid pe pd before entry current snapshot
    Hpe Hpd Htype Hacquire Hread Hrestore.
  unfold q_query_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe),
    (proj2 (Z.eqb_neq _ _) Hpd).
  unfold StateRelMonad.bind, get', get.
  exists before, before; split; [split; reflexivity|].
  rewrite Htype; cbn.
  exists tt, entry; split; [exact Hacquire|].
  exists snapshot, entry; split; [exact Hread|].
  exists tt, current; split; [exact Hrestore|].
  split; reflexivity.
Qed.

Lemma q_query_acquire_type :
  forall critical sg invocation eid mask saved before entry observed current,
  q_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  event_slot_type_value before.(EventState) eid = 2.
Proof.
  intros critical sg invocation eid mask saved before entry observed current
    [_ [_ [_ [Hlookup [_ [Htype _]]]]]].
  unfold event_slot_type_value, mutex_query_lookup in *.
  rewrite Hlookup, Htype; reflexivity.
Qed.

Lemma q_query_api_safe_return :
  forall critical sg invocation eid pe pd before current code snapshot X,
  q_query_program critical sg invocation eid pe pd before (code, snapshot) current ->
  q_query_safe critical sg invocation eid pe pd before X ->
  safeExec (eq current) (StateRelMonad.ret (code, snapshot))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation eid pe pd before current code snapshot X Hprogram Hsafe.
  unfold q_query_safe in Hsafe.
  eapply (highstependret_derive
    (q_query_program critical sg invocation eid pe pd) (eq before)
    (code, snapshot) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

(** A complete endpoint characterization of the ordered program.  In
    particular, errors perform neither interval, and a successful snapshot
    is tied to the acquired state while [current] is the Restore endpoint. *)
Lemma q_query_program_result_iff :
  forall critical sg invocation eid pe pd before result current,
  q_query_program critical sg invocation eid pe pd before result current <->
  if Z.eqb pe 0 then result = (4, None) /\ before = current
  else if Z.eqb pd 0 then result = (9, None) /\ before = current
  else if Z.eqb (event_slot_type_value before.(EventState) eid) 2 then
    exists entry snapshot,
      critical_region_interval critical sg invocation before entry /\
      q_query_critical sg eid entry snapshot entry /\
      critical_region_interval critical sg invocation entry current /\
      result = (0, Some snapshot)
  else result = (1, None) /\ before = current.
Proof.
  intros critical sg invocation eid pe pd before result current.
  unfold q_query_program; destruct (Z.eqb pe 0); [reflexivity|].
  destruct (Z.eqb pd 0); [reflexivity|].
  unfold StateRelMonad.bind, get', get, update, StateRelMonad.ret.
  split.
  - intros [observed [state [[-> <-] Hbranch]]].
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2); [|exact Hbranch].
    destruct Hbranch as [u [entry [Hentry [snapshot [released [Hread
      [v [returned [Hreturn [Hresult Hcurrent]]]]]]]]]].
    pose proof (q_query_critical_kernel_state_eq sg eid entry snapshot released Hread) as ->.
    subst current; exists entry, snapshot; auto.
  - intro Hbranch; exists before, before; split; [split; reflexivity|].
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2); [|exact Hbranch].
    destruct Hbranch as [entry [snapshot [Hentry [Hread [Hreturn Hresult]]]]].
    exists tt, entry; split; [exact Hentry|].
    exists snapshot, entry; split; [exact Hread|].
    exists tt, current; split; [exact Hreturn|]; split; [exact Hresult|reflexivity].
Qed.

(** Non-vacuity uses the original live/free admission and the published
    storage fact already carried by the whole kernel representation.  It
    selects empty environment intervals, not a liveness assumption about
    arbitrary environment executions. *)
Lemma q_query_program_has_result :
  forall critical sg invocation eid pe pd before observed,
  q_query_call_input critical sg invocation pe pd before eid observed ->
  UCOS2_state_inv sg before ->
  queue_published_storage_binding before.(EventState) ->
  exists result, q_query_program critical sg invocation eid pe pd before result before.
Proof.
  intros critical sg invocation eid pe pd before observed Hinput Hvalid Hbinding.
  destruct (Z.eq_dec pe 0) as [->|Hpe].
  - exists (4, None); apply q_query_program_null_event.
  - destruct (Z.eq_dec pd 0) as [->|Hpd].
    + exists (9, None); apply q_query_program_null_output; exact Hpe.
    + destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 2) as [Htype|Htype].
      * destruct (q_query_call_input_live critical sg invocation pe pd before eid observed
          Hinput Hpe Hpd) as [_ [_ [Hslot _]]].
        destruct (q_query_public_slot_is_queue before eid observed Hslot Htype) as [Hlookup Hqtype].
        destruct (q_query_current_fields sg before eid observed Hvalid Hlookup Hqtype)
          as [q [Hq Hconsistent]].
        destruct (q_query_critical_exists sg before eid observed q Hvalid Hbinding
          Hlookup Hqtype Hq) as [snapshot Hread].
        exists (0, Some snapshot); eapply q_query_program_success; eauto; constructor.
      * exists (1, None); apply q_query_program_wrong_type; assumption.
Qed.

(** Same approved observation-loan/closed region as the other public APIs.
    This view does not supply a second independent raw-kernel ownership. *)
Lemma q_query_save_pre_closed : forall critical sg invocation before,
  UCOS2_inv sg before |--
  coq_prop (UCOS2_state_inv sg before) &&
    critical_region_outside critical sg invocation before.
Proof.
  intros; unfold UCOS2_inv, critical_region_outside.
  rewrite critical_region_outside_without_running_rep,
    <- UCOS2_raw_rep_split_running; entailer!.
Qed.

(** A permissive return observation of the registered Restore interface.
    The immediate-return consequence establishes only one legal endpoint;
    actual calls may return after any of the existing registered intervals. *)
Definition q_query_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (released : UCOS2_Verify_State) : Assertion :=
  EX current,
    coq_prop (critical_region_interval critical sg invocation released current) &&
    mutex_query_closed platform critical sg invocation origin
      (armv7a_irq_fiq_mask saved) current.

Lemma q_query_restore_immediate_consequence :
  forall platform critical sg invocation origin saved released,
  mutex_query_closed platform critical sg invocation origin
    (armv7a_irq_fiq_mask saved) released |--
  q_query_restore_post platform critical sg invocation origin saved released.
Proof.
  intros; unfold q_query_restore_post; Exists released.
  assert (critical_region_interval critical sg invocation released released)
    by constructor.
  entailer!.
Qed.

Definition q_query_output_post (pd : addr)
  (snapshot : option QueueQuerySnapshot) : Assertion :=
  match snapshot with
  | None => emp
  | Some copied => q_query_output_fields_rep pd copied
  end.

Definition q_query_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (pe pd code : Z)
  (X : Z -> option QueueQuerySnapshot -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX snapshot current,
    coq_prop (q_query_program critical sg invocation eid pe pd before (code, snapshot) current /\
      safeExec (eq current) (StateRelMonad.ret (code, snapshot))
        (fun result state => X (fst result) (snd result) state)) **
    (mutex_query_closed platform critical sg invocation origin mask current **
     q_query_output_post pd snapshot).
