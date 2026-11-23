Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.lib.mutex_query_spec.
Require Export Ucos2Verify.lib.time.
Require Export Ucos2Verify.lib.tick.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.interrupt.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** OSTimeGet, V2.93.01 Source/os_time.c:237, critical method 3.
    The result is the private scalar copied while masked.  The two existing
    source intervals retain their actual endpoints; in particular Restore
    may advance the clock.  There is no Event handle or task-only guard. *)
Definition time_get_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat)
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (get' time_get) (fun snapshot =>
      StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret snapshot))).

Definition time_get_safe critical sg invocation before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (time_get_program critical sg invocation) X.

Lemma time_get_program_result_iff :
  forall critical sg invocation before snapshot current,
  time_get_program critical sg invocation before snapshot current <->
  exists entry, critical_region_interval critical sg invocation before entry /\
    snapshot = time_get entry /\
    critical_region_interval critical sg invocation entry current.
Proof.
  intros critical sg invocation before snapshot current.
  unfold time_get_program, StateRelMonad.bind, update, get', get, StateRelMonad.ret.
  split.
  - intros [u [entry [Hentry [observed [read_state [[Hobserved Hread]
      [v [returned [Hreturn [Hresult Hcurrent]]]]]]]]]].
    subst read_state; subst returned; subst snapshot; subst observed.
    exists entry; repeat split; assumption.
  - intros [entry [Hentry [Hsnapshot Hreturn]]].
    exists tt, entry; split; [exact Hentry|].
    exists (time_get entry), entry; split; [split; reflexivity|].
    exists tt, current; split; [exact Hreturn|].
    split; [exact Hsnapshot|reflexivity].
Qed.

Lemma time_get_program_observed_return :
  forall critical sg invocation before entry current,
  critical_region_interval critical sg invocation before entry ->
  critical_region_interval critical sg invocation entry current ->
  time_get_program critical sg invocation before (time_get entry) current.
Proof.
  intros; apply time_get_program_result_iff; exists entry; auto.
Qed.

(** An actual no-environment-step execution exists at every abstract state.
    This checks that the program has no hidden validity/closure guard; it
    makes no claim that a concrete Save/Restore call eventually returns. *)
Lemma time_get_program_has_result : forall critical sg invocation before,
  time_get_program critical sg invocation before (time_get before) before.
Proof.
  intros; apply time_get_program_observed_return; constructor.
Qed.

Lemma time_get_safe_return :
  forall critical sg invocation before current snapshot X,
  time_get_program critical sg invocation before snapshot current ->
  time_get_safe critical sg invocation before X ->
  safeExec (eq current) (StateRelMonad.ret snapshot) X.
Proof.
  intros critical sg invocation before current snapshot X Hprogram Hsafe.
  unfold time_get_safe in Hsafe.
  eapply (highstependret_derive (time_get_program critical sg invocation)
    (eq before) snapshot (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Definition time_get_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved.

(** The call-site consequence of the existing Save source/resource contract.
    Validity is transported by the registered client certificates. *)
Lemma time_get_save_consequence :
  forall platform critical sg invocation origin mask saved before entry,
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_raw_rep sg entry |--
  coq_prop (time_get_acquire_facts critical sg invocation mask saved before entry) &&
    (critical_region_masked platform critical sg invocation origin saved entry **
     UCOS2_inv sg entry).
Proof.
  intros platform critical sg invocation origin mask saved before entry Hvalid Hinterval Hsaved.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  unfold time_get_acquire_facts, UCOS2_inv; entailer!.
Qed.

(** The unobserved step-control byte and all other module resources remain
    owned.  Pure range facts originate in the actual acquired Tick invariant. *)
Definition time_get_read_frame (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg entry /\
    0 <= time_get entry < 4294967296 /\
    0 <= entry.(TickState).(tickStepState) < 256) &&
    (sg.(g_OSTickStepState) # UChar |-> entry.(TickState).(tickStepState) **
     UCOS2_raw_rep_missing_tick sg entry).

Lemma time_get_read_split : forall sg entry,
  UCOS2_inv sg entry |--
  coq_prop (0 <= time_get entry <= 4294967295) &&
    (sg.(g_OSTime) # UInt |-> time_get entry ** time_get_read_frame sg entry).
Proof.
  intros; rewrite UCOS2_inv_split_tick.
  unfold time_get_read_frame, tick_inv, store_tick_state, time_get; entailer!; lia.
Qed.

Lemma time_get_read_merge : forall sg entry,
  sg.(g_OSTime) # UInt |-> time_get entry ** time_get_read_frame sg entry |--
    UCOS2_inv sg entry.
Proof.
  intros; rewrite UCOS2_inv_split_tick.
  unfold time_get_read_frame, tick_inv, store_tick_state, time_get; entailer!.
Qed.

Definition time_get_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (released : UCOS2_Verify_State) : Assertion :=
  EX current, coq_prop (critical_region_interval critical sg invocation released current) &&
    mutex_query_closed platform critical sg invocation origin (armv7a_irq_fiq_mask saved) current.

Lemma time_get_restore_consequence :
  forall platform critical sg invocation origin saved released current,
  UCOS2_state_inv sg released ->
  critical_region_interval critical sg invocation released current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation current |--
  time_get_restore_post platform critical sg invocation origin saved released.
Proof.
  intros platform critical sg invocation origin saved released current Hvalid Hinterval.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation released current Hinterval Hvalid)) as Hcurrent.
  unfold time_get_restore_post, mutex_query_closed; Exists current; entailer!.
Qed.

Definition time_get_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (snapshot : Z)
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX current,
    coq_prop (time_get_program critical sg invocation before snapshot current /\
      safeExec (eq current) (StateRelMonad.ret snapshot) X) &&
    mutex_query_closed platform critical sg invocation origin mask current.

Lemma time_get_restore_api_post :
  forall platform critical sg invocation origin mask saved before entry X,
  time_get_acquire_facts critical sg invocation mask saved before entry ->
  time_get_safe critical sg invocation before X ->
  time_get_restore_post platform critical sg invocation origin saved entry |--
    time_get_api_post platform critical sg invocation origin mask before (time_get entry) X.
Proof.
  intros platform critical sg invocation origin mask saved before entry X
    [Hentry [Hvalid [Hsaved Hmask]]] Hsafe.
  unfold time_get_restore_post, time_get_api_post; Intros current.
  match goal with H : critical_region_interval critical sg invocation entry current |- _ =>
    pose proof (time_get_program_observed_return critical sg invocation before entry current Hentry H) as Hprogram
  end.
  pose proof (time_get_safe_return critical sg invocation before current (time_get entry) X Hprogram Hsafe) as Hreturn.
  rewrite Hmask; Exists current; entailer!.
Qed.
