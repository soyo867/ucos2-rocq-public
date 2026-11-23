Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_set_call_spec.

Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Reuse the source-ordered NULL/Type/acquire/count/group prefix exactly.
    Only the two protected results (0 and 73) execute Restore. Its endpoint
    may differ from the checkpoint at which the count and error were stored.
    The Z observation is the caller's error byte, not a C return value. *)
Definition sem_set_source_api_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe count : Z)
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (sem_set_call_program critical sg invocation pe count)
    (fun error => if (Z.eqb error 0 || Z.eqb error 73)%bool then
      StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret error)
      else StateRelMonad.ret error).

Definition sem_set_source_api_safe critical sg invocation pe count before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (sem_set_source_api_program critical sg invocation pe count) X.

Lemma sem_set_source_api_program_result_iff :
  forall critical sg invocation pe count before error after,
  sem_set_source_api_program critical sg invocation pe count before error after <->
  exists checkpoint,
    sem_set_call_program critical sg invocation pe count before error checkpoint /\
    (if (Z.eqb error 0 || Z.eqb error 73)%bool then
      critical_region_interval critical sg invocation checkpoint after
     else checkpoint = after).
Proof.
  intros; unfold sem_set_source_api_program, StateRelMonad.bind, update, StateRelMonad.ret.
  split.
  - intros [code [checkpoint [Hprefix Hsuffix]]].
    destruct (Z.eqb code 0 || Z.eqb code 73)%bool eqn:Hrestore.
    + destruct Hsuffix as [u [returned [Hinterval [-> ->]]]].
      exists checkpoint; rewrite Hrestore; auto.
    + destruct Hsuffix as [-> Hafter].
      exists checkpoint; rewrite Hrestore; auto.
  - intros [checkpoint [Hprefix Hsuffix]].
    exists error, checkpoint; split; [exact Hprefix|].
    destruct (Z.eqb error 0 || Z.eqb error 73)%bool.
    + exists tt, after; split; [exact Hsuffix|]; split; reflexivity.
    + split; [reflexivity|exact Hsuffix].
Qed.

Lemma sem_set_source_api_null_return : forall critical sg invocation count before,
  sem_set_source_api_program critical sg invocation 0 count before 4 before.
Proof.
  intros; apply sem_set_source_api_program_result_iff; exists before.
  split; [apply sem_set_call_null_return|reflexivity].
Qed.

Lemma sem_set_source_api_wrong_type_return :
  forall critical sg invocation pe count before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  event_slot_type_value before.(EventState) eid <> 3 ->
  sem_set_source_api_program critical sg invocation pe count before 1 before.
Proof.
  intros; apply sem_set_source_api_program_result_iff; exists before.
  split; [eapply sem_set_call_wrong_type_return; eassumption|reflexivity].
Qed.

Lemma sem_set_source_api_restored_return :
  forall critical sg invocation pe count before eid observed mask saved entry current after,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  critical_region_interval critical sg invocation (sem_set_checkpoint entry eid current count) after ->
  sem_set_source_api_program critical sg invocation pe count before (sem_set_error entry current) after.
Proof.
  intros; apply sem_set_source_api_program_result_iff.
  exists (sem_set_checkpoint entry eid current count); split.
  - eapply sem_set_call_checkpoint_return; eassumption.
  - unfold sem_set_error; destruct (sem_set_can_write entry current); exact H3.
Qed.

Lemma sem_set_source_api_safe_return :
  forall critical sg invocation pe count before error after X,
  sem_set_source_api_program critical sg invocation pe count before error after ->
  sem_set_source_api_safe critical sg invocation pe count before X ->
  safeExec (eq after) (StateRelMonad.ret error) X.
Proof.
  intros critical sg invocation pe count before error after X Hprogram Hsafe.
  unfold sem_set_source_api_safe in Hsafe.
  eapply (highstependret_derive
    (sem_set_source_api_program critical sg invocation pe count) (eq before)
    error (fun _ => eq after)); [|exact Hsafe].
  intros state Hstate; subst state; exists after; split; assumption || reflexivity.
Qed.

Lemma sem_set_source_api_preserves_validity :
  forall critical sg invocation pe count before error after,
  UCOS2_state_inv sg before -> 0 <= count <= 65535 ->
  sem_set_source_api_program critical sg invocation pe count before error after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation pe count before error after Hvalid Hcount Hprogram.
  apply sem_set_source_api_program_result_iff in Hprogram.
  destruct Hprogram as [checkpoint [Hprefix Hsuffix]].
  assert (Hcheckpoint : UCOS2_state_inv sg checkpoint).
  { destruct Hprefix as [[_ [_ ->]]|[_ [eid [observed [_ [_ [_ Hbranch]]]]]]];
      [exact Hvalid|].
    destruct Hbranch as [[_ [_ ->]]|[_ [_ [entry [current
      [Hinterval [Hlookup [Htype [_ [_ ->]]]]]]]]]]; [exact Hvalid|].
    eapply sem_set_checkpoint_preserves_validity; try eassumption.
    exact (proj1 (critical_region_interval_transports_resources
      critical sg invocation before entry Hinterval Hvalid)). }
  destruct (Z.eqb error 0 || Z.eqb error 73)%bool.
  - exact (proj1 (critical_region_interval_transports_resources
      critical sg invocation checkpoint after Hsuffix Hcheckpoint)).
  - subst after; exact Hcheckpoint.
Qed.

Lemma sem_set_source_api_error_cases : forall critical sg invocation pe count before error after,
  sem_set_source_api_program critical sg invocation pe count before error after ->
  error = 4 \/ error = 1 \/ error = 0 \/ error = 73.
Proof.
  intros; apply sem_set_source_api_program_result_iff in H.
  destruct H as [checkpoint [Hprefix _]].
  destruct Hprefix as [[_ [-> _]]|[_ [eid [observed [_ [_ [_ Hbranch]]]]]]]; [auto|].
  destruct Hbranch as [[_ [-> _]]|[_ [_ [entry [current [_ [_ [_ [_ [-> _]]]]]]]]]];
    [auto|].
  unfold sem_set_error; destruct (sem_set_can_write entry current); auto.
Qed.

(** Mathematical non-vacuity over the unchanged call domain; reflexive
    intervals do not assert that platform execution eventually returns. *)
Lemma sem_set_source_api_program_has_result :
  forall critical sg invocation pe count before eid observed,
  UCOS2_state_inv sg before ->
  sem_set_call_input critical sg invocation pe before eid observed ->
  exists error after, sem_set_source_api_program critical sg invocation pe count before error after.
Proof.
  intros critical sg invocation pe count before eid observed Hvalid Hinput.
  destruct Hinput as [->|[Hpe [Haddr [Hid [Hslot Hprotocol]]]]].
  - exists 4, before; apply sem_set_source_api_null_return.
  - destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 3) as [Htype|Htype].
    + destruct (sem_query_public_slot_is_sem before eid observed Hslot Htype) as [Hlookup Hsem].
      exists (sem_set_error before observed), (sem_set_checkpoint before eid observed count).
      eapply sem_set_source_api_restored_return with
        (mask := 0) (saved := 0) (entry := before) (current := observed); try eassumption.
      * unfold sem_query_acquire_facts; split; [constructor|].
        split; [exact Hvalid|]; split.
        { unfold interrupt_saved_value, valid_os_cpu_sr, armv7a_irq_fiq_mask; cbn; lia. }
        repeat split; assumption || reflexivity.
      * constructor.
    + exists 1, before; eapply sem_set_source_api_wrong_type_return; eassumption.
Qed.

(** The saved token remains indexed by the acquired entry. Shared bytes and
    validity describe the actual checkpoint passed to modular Restore. *)
Definition sem_set_source_api_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask saved : Z)
  (entry checkpoint : UCOS2_Verify_State) : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\ UCOS2_state_inv sg checkpoint) &&
  (critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_inv sg checkpoint).

Definition sem_set_source_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (pe count pd : Z)
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX error after,
    coq_prop (sem_set_source_api_program critical sg invocation pe count before error after /\
      safeExec (eq after) (StateRelMonad.ret error) X) **
    (mutex_query_closed platform critical sg invocation origin mask after ** pd # UChar |-> error).
