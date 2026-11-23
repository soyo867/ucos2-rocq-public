Require Export Ucos2Verify.VC.code.mutex.spec.mutex_accept_modular_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_spec.
Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only the protected Accept paths call Restore.  Their result code is
    either NONE (including an unavailable mutex) or PCP_LOWER.  The three
    early error paths return before Save and keep the input state. *)
Lemma mutex_accept_protected_result_codes : forall sg eid entry current code value checkpoint,
  mutex_accept_protected_result sg eid entry current code value checkpoint ->
  code = 0 \/ code = 120.
Proof.
  intros * [mutex [_ [Hbusy | [_ [tid [task Howned]]]]]].
  - tauto.
  - destruct Howned as [_ [_ [_ [_ [Hlower | Hnormal]]]]]; tauto.
Qed.

Lemma mutex_accept_public_program_result_cases : forall critical sg invocation pe before code value checkpoint,
  mutex_accept_public_program critical sg invocation pe before (code, value) checkpoint ->
  (code = 0 \/ code = 120) \/
  ((code = 1 \/ code = 2 \/ code = 4) /\ checkpoint = before).
Proof.
  intros * [Hcall | [_ [eid [_ [_ [_ [_ [Hresult Hstate]]]]]]]].
  - destruct Hcall as [[_ [Hresult Hstate]] | [_ [eid [observed [_ [_ [_ Hbranch]]]]]]].
    + inversion Hresult; subst; tauto.
    + destruct Hbranch as [[_ [Hresult Hstate]] | [_ [[_ [Hresult Hstate]] | [_ [entry [current [_ [_ [_ [_ Hprotected]]]]]]]]]].
      * inversion Hresult; subst; tauto.
      * inversion Hresult; subst; tauto.
      * left; eapply mutex_accept_protected_result_codes; exact Hprotected.
  - inversion Hresult; subst; tauto.
Qed.

Definition mutex_accept_return_program critical sg invocation pe
  : program UCOS2_Verify_State (Z * Z) :=
  fun before result after => exists checkpoint,
    mutex_accept_public_program critical sg invocation pe before result checkpoint /\
    (if orb (Z.eqb (fst result) 0) (Z.eqb (fst result) 120)
     then critical_region_interval critical sg invocation checkpoint after
     else after = checkpoint).

Definition mutex_accept_return_post_prop critical sg invocation pe before code value after : Prop :=
  mutex_accept_return_program critical sg invocation pe before (code, value) after.

Lemma mutex_accept_return_protected : forall critical sg invocation pe before code value checkpoint after,
  mutex_accept_public_program critical sg invocation pe before (code, value) checkpoint ->
  (code = 0 \/ code = 120) ->
  critical_region_interval critical sg invocation checkpoint after ->
  mutex_accept_return_program critical sg invocation pe before (code, value) after.
Proof.
  intros * Hprogram Hcode Hinterval; exists checkpoint; split; [exact Hprogram |].
  destruct Hcode as [-> | ->]; exact Hinterval.
Qed.

Lemma mutex_accept_return_early : forall critical sg invocation pe before code value checkpoint,
  mutex_accept_public_program critical sg invocation pe before (code, value) checkpoint ->
  code <> 0 -> code <> 120 ->
  mutex_accept_return_program critical sg invocation pe before (code, value) checkpoint.
Proof.
  intros * Hprogram Hzero Hlower; exists checkpoint; split; [exact Hprogram |].
  apply Z.eqb_neq in Hzero; apply Z.eqb_neq in Hlower.
  cbn; rewrite Hzero, Hlower; reflexivity.
Qed.

Lemma mutex_accept_return_early_state : forall critical sg invocation pe before code value after,
  mutex_accept_return_program critical sg invocation pe before (code, value) after ->
  code <> 0 -> code <> 120 ->
  after = before /\ (code = 1 \/ code = 2 \/ code = 4).
Proof.
  intros * [checkpoint [Hprogram Hend]] Hzero Hlower.
  destruct (mutex_accept_public_program_result_cases _ _ _ _ _ _ _ _ Hprogram)
    as [Hprotected | [Hcode Hstate]]; [tauto |].
  apply Z.eqb_neq in Hzero; apply Z.eqb_neq in Hlower.
  cbn in Hend; rewrite Hzero, Hlower in Hend; split; congruence.
Qed.

Lemma mutex_accept_return_safe_return : forall critical sg invocation pe before after code value X,
  mutex_accept_return_program critical sg invocation pe before (code, value) after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_accept_return_program critical sg invocation pe)) mutex_accept_observe_result) X ->
  safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z value) X.
Proof.
  intros * Hprogram Hsafe.
  eapply (mutex_accept_safe_return__restore_and_returns (Z * Z) Z
    (mutex_accept_return_program critical sg invocation pe) mutex_accept_observe_result
    before after (code, value) value X).
  - exact Hprogram.
  - intros P; unfold mutex_accept_observe_result; split; reflexivity.
  - exact Hsafe.
Qed.

(** The interval and returned heap are opened from this actual Restore's
    existing postcondition.  They are not a new caller promise. *)
Lemma mutex_accept_call_return_complete : forall environment platform critical saved_local sg original
  invocation origin mask pe before code value checkpoint X,
  mutex_accept_public_program critical sg invocation pe before (code, value) checkpoint ->
  (code = 0 \/ code = 120) ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_accept_return_program critical sg invocation pe)) mutex_accept_observe_result) X ->
  mutex_accept_call_return environment platform critical saved_local sg original
    invocation origin mask checkpoint |--
  EX after,
    coq_prop (mutex_accept_return_program critical sg invocation pe before (code, value) after /\
      safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z value) X) &&
    (mutex_accept_closed platform critical sg invocation origin mask after **
      mutex_accept_call_support environment saved_local sg original after).
Proof.
  intros * Hprogram Hcode Hsafe.
  unfold mutex_accept_call_return; Intros after.
  assert (Hreturned : mutex_accept_return_program critical sg invocation pe before (code, value) after).
  { eapply mutex_accept_return_protected; eassumption. }
  pose proof (mutex_accept_return_safe_return _ _ _ _ _ _ _ _ _ Hreturned Hsafe) as Hsafe_after.
  Exists after; entailer!.
Qed.
