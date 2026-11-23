Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.lib.time.
Require Export Ucos2Verify.lib.tick.
Require Export Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.lib.ucos2_state_machine.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** OSTimeSet, V2.93.01: acquire, write the UInt clock, then Restore.
    The two environment intervals are the existing C modular contracts.
    They are not identities and do not promise eventual return. *)
Definition time_set_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (ticks : Z)
  : program UCOS2_Verify_State unit :=
  StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (update' (fun entry => time_set_state entry ticks))
      (fun _ => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret tt))).

Definition time_set_post (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (ticks : Z) (after : UCOS2_Verify_State) : Prop :=
  exists entry, critical_region_interval critical sg invocation before entry /\
    critical_region_interval critical sg invocation (time_set_state entry ticks) after.

Definition time_set_safe critical sg invocation before ticks
  (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (time_set_program critical sg invocation ticks) X.

Definition time_set_return_safe (after : UCOS2_Verify_State)
  (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq after) (StateRelMonad.ret tt) X.

Lemma time_set_program_result_iff : forall critical sg invocation ticks before result after,
  time_set_program critical sg invocation ticks before result after <->
  result = tt /\ time_set_post critical sg invocation before ticks after.
Proof.
  intros critical sg invocation ticks before result after.
  unfold time_set_program, time_set_post, StateRelMonad.bind,
    update', update, StateRelMonad.ret.
  split.
  - intros [u [entry [Hacquire [v [checkpoint [Hwrite
      [w [current [Hrestore [Hresult Hafter]]]]]]]]]].
    change (checkpoint = time_set_state entry ticks) in Hwrite.
    subst checkpoint; subst current; split; [exact Hresult|].
    exists entry; split; assumption.
  - intros [Hresult [entry [Hacquire Hrestore]]].
    exists tt, entry; split; [exact Hacquire|].
    exists tt, (time_set_state entry ticks); split; [reflexivity|].
    exists tt, after; split; [exact Hrestore|]; split; [exact Hresult|reflexivity].
Qed.

(** The abstract source path has a successor even for zero/decreasing ticks.
    A reflexive possible environment path is not a platform liveness claim. *)
Lemma time_set_program_has_result : forall critical sg invocation ticks before,
  time_set_program critical sg invocation ticks before tt (time_set_state before ticks).
Proof.
  intros; apply time_set_program_result_iff; split; [reflexivity|].
  exists before; split;
    unfold critical_region_interval, kernel_resumption_trace; constructor.
Qed.

Lemma time_set_safe_return : forall critical sg invocation before ticks after X,
  time_set_post critical sg invocation before ticks after ->
  time_set_safe critical sg invocation before ticks X ->
  time_set_return_safe after X.
Proof.
  intros critical sg invocation before ticks after X Hpost Hsafe.
  unfold time_set_safe in Hsafe; unfold time_set_return_safe.
  eapply (highstependret_derive (time_set_program critical sg invocation ticks)
    (eq before) tt (fun _ => eq after)); [|exact Hsafe].
  intros state Hstate; subst state; exists after; split; [|reflexivity].
  apply time_set_program_result_iff; split; [reflexivity|exact Hpost].
Qed.

Definition time_set_written (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before entry checkpoint : UCOS2_Verify_State)
  (ticks : Z) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  checkpoint = time_set_state entry ticks.

Lemma time_set_restored_return : forall critical sg invocation before entry checkpoint ticks after,
  time_set_written critical sg invocation before entry checkpoint ticks ->
  critical_region_interval critical sg invocation checkpoint after ->
  time_set_post critical sg invocation before ticks after.
Proof.
  intros critical sg invocation before entry checkpoint ticks after [Hacquire ->] Hrestore.
  exists entry; split; assumption.
Qed.

(** This is a focused residual of the existing TickModule, not a new clock
    owner. The acquisition-indexed inside token is deliberately retained. *)
Definition time_set_store_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Assertion :=
  coq_prop (critical_region_interval critical sg invocation before entry /\
    UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
    0 <= entry.(TickState).(tickStepState) < 256) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   sg.(g_OSTickStepState) # UChar |-> entry.(TickState).(tickStepState) **
   UCOS2_raw_rep_missing_tick sg entry).

Lemma time_set_inv_split_clock : forall platform critical sg invocation origin mask saved before entry,
  critical_region_interval critical sg invocation before entry ->
  UCOS2_state_inv sg entry -> interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_inv sg entry |--
  sg.(g_OSTime) # UInt |-> time_get entry **
    time_set_store_frame platform critical sg invocation origin mask saved before entry.
Proof.
  intros platform critical sg invocation origin mask saved before entry Hinterval Hvalid Hsaved.
  rewrite (UCOS2_inv_split_tick sg entry).
  unfold tick_inv, store_tick_state, time_get, time_set_store_frame.
  Intros; entailer!.
Qed.

Lemma time_set_missing_tick_eq : forall sg entry ticks,
  UCOS2_raw_rep_missing_tick sg entry =
    UCOS2_raw_rep_missing_tick sg (time_set_state entry ticks).
Proof.
  intros sg entry ticks; unfold UCOS2_raw_rep_missing_tick.
  apply UCOS2_raw_rep_missing_module_frame.
  intros owner Howner; destruct owner; try reflexivity; contradiction.
Qed.

Lemma time_set_selected_frame : forall sg entry ticks owner,
  UCOS2_state_inv sg entry -> 0 <= ticks < 4294967296 ->
  tick_modules owner = false ->
  UCOS2_module_rep sg entry owner |--
    UCOS2_module_rep sg (time_set_state entry ticks) owner.
Proof.
  intros sg entry ticks owner Hvalid Hticks Howner.
  exact (selected_transition_frame sg tick_modules _ (time_set_selected_transition sg)
    entry (time_set_state entry ticks) Hvalid (ex_intro _ ticks (conj Hticks eq_refl))
    owner Howner).
Qed.

Lemma time_set_inv_merge_updated_clock : forall sg entry ticks,
  UCOS2_state_inv sg entry -> 0 <= ticks < 4294967296 ->
  0 <= entry.(TickState).(tickStepState) < 256 ->
  sg.(g_OSTime) # UInt |-> ticks **
    sg.(g_OSTickStepState) # UChar |-> entry.(TickState).(tickStepState) **
    UCOS2_raw_rep_missing_tick sg entry |-- UCOS2_inv sg (time_set_state entry ticks).
Proof.
  intros sg entry ticks Hvalid Hticks Hstep.
  pose proof (time_set_preserves_validity sg entry ticks Hvalid) as Hupdated.
  rewrite (UCOS2_inv_split_tick sg (time_set_state entry ticks)).
  rewrite <- time_set_missing_tick_eq.
  unfold tick_inv, store_tick_state; cbn [time_set_state replace_TickS TickState ostime tickStepState].
  entailer!.
Qed.

Lemma time_set_store_frame_merge_updated :
  forall platform critical sg invocation origin mask saved before entry ticks,
  0 <= ticks < 4294967296 ->
  sg.(g_OSTime) # UInt |-> ticks **
    time_set_store_frame platform critical sg invocation origin mask saved before entry |--
  coq_prop (time_set_written critical sg invocation before entry (time_set_state entry ticks) ticks) &&
    mbox_accept_cpu_restore_pre platform critical sg invocation origin mask saved
      entry (time_set_state entry ticks).
Proof.
  intros platform critical sg invocation origin mask saved before entry ticks Hticks.
  unfold time_set_store_frame; Intros.
  match goal with H : critical_region_interval _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hacquire [Hvalid [Hsaved Hstep]]] end.
  pose proof (time_set_preserves_validity sg entry ticks Hvalid) as Hupdated.
  sep_apply_l_atomic (time_set_inv_merge_updated_clock sg entry ticks Hvalid Hticks Hstep).
  unfold time_set_written, mbox_accept_cpu_restore_pre; entailer!.
Qed.
