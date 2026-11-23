Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.

(** V2.93.01 OSSemAccept: conditional NULL check, unconditional type
    check, Save, read the old UShort count, conditionally decrement,
    Restore, return the saved count.  No ISR/lock guard or output cell. *)
Definition sem_accept_argument_rejected (sg : StableGlobVars) (pevent : addr) : bool :=
  (sg.(osKernelConfig).(cfgArgumentChecks) && Z.eqb pevent 0)%bool.

Definition sem_accept_type_rejected (type_byte : Z) : bool :=
  negb (Z.eqb type_byte (encode_event_type OS_EVENT_TYPE_SEM)).

Definition sem_accept_critical (sg : StableGlobVars) (eid : EventID)
  : program UCOS2_Verify_State Z :=
  fun s count after => exists e fields,
    s.(EventState).(inUsedEventStates) eid = Some e /\ e.(semFields) = Some fields /\
    count = fields.(semCount) /\
    after = if Z.ltb 0 fields.(semCount)
            then sem_count_update_state s eid e (fields.(semCount) - 1) else s.

Lemma sem_accept_critical_exists : forall sg s eid e fields,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(semFields) = Some fields ->
  exists count after, sem_accept_critical sg eid s count after.
Proof.
  intros sg s eid e fields He Hfields; eexists _, _; exists e, fields; repeat split; eauto.
Qed.

Lemma sem_accept_critical_deterministic : forall sg eid s count1 after1 count2 after2,
  sem_accept_critical sg eid s count1 after1 -> sem_accept_critical sg eid s count2 after2 ->
  count1 = count2 /\ after1 = after2.
Proof.
  intros sg eid s count1 after1 count2 after2 [e1 [f1 [He1 [Hf1 [-> ->]]]]]
    [e2 [f2 [He2 [Hf2 [-> ->]]]]].
  assert (e2 = e1) by congruence; subst e2; assert (f2 = f1) by congruence; subst f2;
    split; reflexivity.
Qed.

Lemma sem_accept_critical_preserves_validity : forall sg s eid e count after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> sem_accept_critical sg eid s count after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg s eid e count after Hvalid He Htype [node [fields [Hnode [Hfields [_ ->]]]]].
  assert (node = e) by congruence; subst node.
  destruct (Z.ltb 0 fields.(semCount)) eqn:Hpositive; [|exact Hvalid].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hcount; unfold event_payload_consistency in Hcount.
  rewrite Htype, Hfields in Hcount; apply Z.ltb_lt in Hpositive.
  apply UCOS2_sem_count_update_preserves_validity; try assumption.
  apply sem_decrement_preserves_consistency; assumption.
Qed.

Lemma sem_accept_critical_returns_old_count : forall sg s eid e fields count after,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(semFields) = Some fields ->
  sem_accept_critical sg eid s count after -> count = fields.(semCount).
Proof.
  intros sg s eid e fields count after He Hfields [node [before [Hnode [Hbefore [Hcount _]]]]];
    congruence.
Qed.

Lemma sem_accept_critical_zero_frame : forall sg eid s after,
  sem_accept_critical sg eid s 0 after -> after = s.
Proof.
  intros sg eid s after [e [fields [_ [_ [Hcount ->]]]]].
  rewrite <- Hcount; reflexivity.
Qed.

Lemma sem_accept_critical_result_in_range : forall sg s eid e count after,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM -> sem_accept_critical sg eid s count after ->
  0 <= count <= 65535.
Proof.
  intros sg s eid e count after Hvalid He Htype
    [node [fields [Hnode [Hfields [-> _]]]]].
  assert (node = e) by congruence; subst node.
  destruct Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid e He); unfold event_payload_consistency in Hpayload.
  rewrite Htype, Hfields in Hpayload; exact (proj1 Hpayload).
Qed.

(** These are guarantees of this count operation, not a claim that arbitrary
    environment clients preserve a published handle.  In particular the
    semaphore count may change even though its generation and type do not. *)
Lemma sem_accept_critical_preserves_event_identity :
  forall sg eid before count after observed previous,
  sem_accept_critical sg eid before count after ->
  before.(EventState).(inUsedEventStates) observed = Some previous ->
  exists current,
    after.(EventState).(inUsedEventStates) observed = Some current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros sg eid before count after observed previous
    [node [fields [Hnode [_ [_ ->]]]]] Hprevious.
  destruct (Z.ltb 0 fields.(semCount)).
  - unfold sem_count_update_state, replace_EventS, update_event_field_raw; cbn.
    destruct (Z.eqb observed eid) eqn:Hsame.
    + apply Z.eqb_eq in Hsame; subst observed.
      assert (previous = node) by congruence; subst previous.
      exists (sem_set_count node (fields.(semCount) - 1)); repeat split; reflexivity.
    + exists previous; split; [exact Hprevious|split; reflexivity].
  - exists previous; split; [exact Hprevious|split; reflexivity].
Qed.

Lemma sem_accept_critical_frame_other_event :
  forall sg eid before count after other,
  sem_accept_critical sg eid before count after -> other <> eid ->
  after.(EventState).(inUsedEventStates) other =
    before.(EventState).(inUsedEventStates) other.
Proof.
  intros sg eid before count after other [node [fields [_ [_ [_ ->]]]]] Hother.
  destruct (Z.ltb 0 fields.(semCount)); [|reflexivity].
  unfold sem_count_update_state, replace_EventS, update_event_field_raw; cbn.
  destruct (Z.eqb other eid) eqn:Hsame; [apply Z.eqb_eq in Hsame; contradiction|reflexivity].
Qed.

Lemma sem_accept_critical_preserves_invocation : forall sg eid s count after invocation origin,
  sem_accept_critical sg eid s count after ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg eid s count after invocation origin [e [fields [_ [_ [_ ->]]]]] Hactive;
    destruct (Z.ltb 0 fields.(semCount)); exact Hactive.
Qed.

(** The selected C retains the NULL guard.  This is a function/profile
    binding, not an extra restriction on every kernel configuration. *)
Definition sem_accept_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true.

(** A source client for the protected count operation.  The type fact is
    supplied by the earlier C check and its handle-lifetime protocol;
    no invariant or desired postcondition is added to the operation guard.
    Neither Task nor private Event creation resources are changed. *)
Definition sem_accept_critical_client (invocation : nat) (eid : EventID)
  (count : Z) : KernelClientAction :=
  {| kernel_client_actor := Some invocation;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after => exists e,
       before.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       sem_accept_critical sg eid before count after |}.

Lemma sem_accept_critical_client_certificate : forall invocation eid count,
  KernelClientCertificate (sem_accept_critical_client invocation eid count).
Proof.
  intros invocation eid count; constructor.
  - intros sg before after Hvalid [e [He [Htype Hstep]]].
    eapply sem_accept_critical_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [e [He [Htype Hstep]]] Hforeign.
    destruct Hstep as [node [fields [_ [_ [_ ->]]]]].
    destruct (Z.ltb 0 fields.(semCount)); reflexivity.
  - intros sg before after observer origin Hvalid [e [He [Htype Hstep]]]
      Hnormal Hactive.
    eapply sem_accept_critical_preserves_invocation; eassumption.
  - intros sg before after observer Hvalid [e [He [Htype Hstep]]] Hforeign.
    destruct Hstep as [node [fields [_ [_ [_ ->]]]]].
    destruct (Z.ltb 0 fields.(semCount)); reflexivity.
Qed.
