Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.event Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_accept_call_spec.

Import UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Whole source call: the pre-Save type observation, protected count
    operation, and Restore interval have distinct endpoints. Both zero and
    positive counts execute Restore; NULL and wrong-Type return directly.
    The saved local count is not re-read after interrupts are restored. *)
Definition sem_accept_source_api_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  : program UCOS2_Verify_State Z :=
  fun before count after =>
    (pevent = 0 /\ count = 0 /\ after = before) \/
    (pevent <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\
      sem_accept_lookup before eid observed /\
      ((observed.(eventType) <> OS_EVENT_TYPE_SEM /\ count = 0 /\ after = before) \/
       (observed.(eventType) = OS_EVENT_TYPE_SEM /\ exists entry current checkpoint,
        critical_region_interval critical sg invocation before entry /\
        sem_accept_lookup entry eid current /\
        current.(eventType) = OS_EVENT_TYPE_SEM /\
        current.(eventGeneration) = observed.(eventGeneration) /\
        sem_accept_critical sg eid entry count checkpoint /\
        critical_region_interval critical sg invocation checkpoint after))).

Definition sem_accept_source_api_safe critical sg invocation pe before X : Prop :=
  safeExec (fun state => state = before)
    (sem_accept_source_api_program critical sg invocation pe) X.

Definition sem_accept_source_api_return_safe after count
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = after) (ret count) X.

Definition sem_accept_source_api_post critical sg invocation pe before count after : Prop :=
  sem_accept_source_api_program critical sg invocation pe before count after.

Lemma sem_accept_source_api_safe_return : forall critical sg invocation pe before count after X,
  sem_accept_source_api_safe critical sg invocation pe before X ->
  sem_accept_source_api_post critical sg invocation pe before count after ->
  sem_accept_source_api_return_safe after count X.
Proof.
  intros critical sg invocation pe before count after X Hsafe Hstep.
  unfold sem_accept_source_api_safe in Hsafe; unfold sem_accept_source_api_return_safe.
  eapply highstependret_derive with
    (c1 := sem_accept_source_api_program critical sg invocation pe)
    (P := fun state => state = before)
    (P' := fun (_ : Z) state => state = after).
  - intros state ->; exists after; split; [exact Hstep|reflexivity].
  - exact Hsafe.
Qed.

Lemma sem_accept_source_api_null_return : forall critical sg invocation before,
  sem_accept_source_api_post critical sg invocation 0 before 0 before.
Proof. intros; left; auto. Qed.

Lemma sem_accept_source_api_wrong_type_return : forall critical sg invocation pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_accept_lookup before eid observed ->
  observed.(eventType) <> OS_EVENT_TYPE_SEM ->
  sem_accept_source_api_post critical sg invocation pe before 0 before.
Proof.
  intros critical sg invocation pe before eid observed Hpe Haddr Hid Hlookup Htype.
  right; split; [exact Hpe|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hlookup|].
  left; auto.
Qed.

Lemma sem_accept_source_api_restored_return :
  forall critical sg invocation pe before eid observed mask saved entry current after,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_accept_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  critical_region_interval critical sg invocation (sem_accept_checkpoint entry eid current) after ->
  sem_accept_source_api_post critical sg invocation pe before (encode_event_cnt_value current) after.
Proof.
  intros critical sg invocation pe before eid observed mask saved entry current after
    Hpe Haddr Hid [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]]
    Hrestore.
  right; split; [exact Hpe|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hbefore|].
  right; split; [exact Htype|]; exists entry, current, (sem_accept_checkpoint entry eid current).
  split; [exact Hinterval|]; split; [exact Hlookup|]; split; [exact Hcurrent|].
  split; [exact Hgen|]; split; [|exact Hrestore].
  apply sem_accept_checkpoint_critical; assumption.
Qed.

Lemma sem_accept_source_api_preserves_validity : forall critical sg invocation pe before count after,
  UCOS2_state_inv sg before ->
  sem_accept_source_api_post critical sg invocation pe before count after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation pe before count after Hvalid
    [[_ [_ ->]]|[_ [eid [observed [_ [_ [Hlookup Hbranch]]]]]]]; [exact Hvalid|].
  destruct Hbranch as [[_ [_ ->]]|[Htype [entry [current [checkpoint
    [Hinterval [Hentry [Hcurrent [Hgen [Hstep Hrestore]]]]]]]]]]; [exact Hvalid|].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry_valid.
  pose proof (sem_accept_critical_preserves_validity sg entry eid current count checkpoint
    Hentry_valid Hentry Hcurrent Hstep) as Hcheckpoint_valid.
  exact (proj1 (critical_region_interval_transports_resources
    critical sg invocation checkpoint after Hrestore Hcheckpoint_valid)).
Qed.

Lemma sem_accept_source_api_result_in_range : forall critical sg invocation pe before count after,
  UCOS2_state_inv sg before ->
  sem_accept_source_api_post critical sg invocation pe before count after ->
  0 <= count <= 65535.
Proof.
  intros critical sg invocation pe before count after Hvalid
    [[_ [-> _]]|[_ [eid [observed [_ [_ [Hlookup Hbranch]]]]]]]; [lia|].
  destruct Hbranch as [[_ [-> _]]|[Htype [entry [current [checkpoint
    [Hinterval [Hentry [Hcurrent [Hgen [Hstep Hrestore]]]]]]]]]]; [lia|].
  eapply sem_accept_critical_result_in_range; [|exact Hentry|exact Hcurrent|exact Hstep].
  exact (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)).
Qed.

(** No post-invariant or progress guard is added to the source relation.
    Reflexive environment intervals give a mathematical endpoint for every
    admitted input. This does not assert that platform execution terminates. *)
Lemma sem_accept_source_api_program_has_result : forall critical sg invocation pe before eid observed,
  UCOS2_state_inv sg before ->
  sem_accept_call_input critical sg invocation pe before eid observed ->
  exists count after, sem_accept_source_api_program critical sg invocation pe before count after.
Proof.
  intros critical sg invocation pe before eid observed Hvalid Hinput.
  destruct Hinput as [->|[Hpe [Haddr [Hid [Hlookup Hprotocol]]]]].
  - exists 0, before; apply sem_accept_source_api_null_return.
  - destruct (eventType observed) eqn:Htype;
      try solve [exists 0, before; eapply sem_accept_source_api_wrong_type_return;
        try eassumption; congruence].
    exists (encode_event_cnt_value observed), (sem_accept_checkpoint before eid observed).
    eapply sem_accept_source_api_restored_return with
      (mask := 0) (saved := 0) (entry := before) (current := observed);
      try eassumption.
    + unfold sem_accept_acquire_facts; split.
      * unfold critical_region_interval, kernel_resumption_trace; constructor.
      * split; [exact Hvalid|]. split.
        { unfold interrupt_saved_value, valid_os_cpu_sr, armv7a_irq_fiq_mask; cbn; lia. }
        repeat split; assumption || reflexivity.
    + unfold critical_region_interval, kernel_resumption_trace; constructor.
Qed.

(** The actual C modular Restore input: the saved token is indexed by the
    acquired entry, while all shared bytes and validity describe the written
    checkpoint. The callee returns an interval and closed resources at ONE
    actual after; no state equality or eventual return is assumed. *)
Definition sem_accept_source_api_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask saved : Z)
  (entry checkpoint : UCOS2_Verify_State) : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\ UCOS2_state_inv sg checkpoint) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   UCOS2_inv sg checkpoint).
