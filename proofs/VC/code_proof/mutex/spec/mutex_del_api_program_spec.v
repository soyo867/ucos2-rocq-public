Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_continuation_spec.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Keep the established ordering: unmasked early checks, the actual Save
    owner history, the acquired type recheck, protected deletion, Restore,
    and optional OS_Sched. The historical checkpoint is not the returned
    world. The pair records both the returned pointer and the written byte. *)
Definition mutex_del_api_program environment critical sg original pe option eid
  : program UCOS2_Verify_State (Z * Z) :=
  fun before result after =>
    match mutex_del_before_save_error pe (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) with
    | Some (pointer, error) => result = (pointer, encode_os_err_code error) /\ after = before
    | None =>
        (exists acquired kind returned,
          mutex_owner_source_history sg before acquired /\
          mutex_del_runtime_type_observation sg eid acquired kind /\ kind <> 4 /\
          result = (pe, encode_os_err_code OS_ERR_EVENT_TYPE) /\
          mutex_api_restore_history environment critical sg original acquired returned after) \/
        (exists acquired checkpoint request returned,
          mutex_owner_source_history sg before acquired /\
          mutex_del_parent_critical_observation sg eid option (fst result) (snd result)
            request acquired checkpoint /\
          mutex_api_tail_history environment critical sg original checkpoint request returned after)
    end.

Definition mutex_del_api_observe_result (result : Z * Z)
  : program (UCOS2_Verify_State -> Prop) Z := StateRelMonad.ret (fst result).

Definition mutex_del_api_refinement_pre environment critical sg original pe option eid before X : Prop :=
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_del_api_program environment critical sg original pe option eid))
      mutex_del_api_observe_result) X.

Definition mutex_del_api_return_post environment external platform critical saved_local
  sg original mask before pe option eid pointer code X : Assertion :=
  EX returned after,
    coq_prop (mutex_del_api_program environment critical sg original pe option eid
        before (pointer, code) after /\
      safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z pointer) X) &&
    mutex_del_continuation_return_at environment external platform saved_local
      sg original mask returned after.

Lemma mutex_del_api_program_early :
  forall environment critical sg original pe option eid before pointer error,
  mutex_del_before_save_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) = Some (pointer, error) ->
  mutex_del_api_program environment critical sg original pe option eid
    before (pointer, encode_os_err_code error) before.
Proof. intros; unfold mutex_del_api_program; rewrite H; auto. Qed.

Lemma mutex_del_api_program_type_error :
  forall environment critical sg original pe option eid before acquired kind returned after,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_owner_source_history sg before acquired ->
  mutex_del_runtime_type_observation sg eid acquired kind -> kind <> 4 ->
  mutex_api_restore_history environment critical sg original acquired returned after ->
  mutex_del_api_program environment critical sg original pe option eid
    before (pe, encode_os_err_code OS_ERR_EVENT_TYPE) after.
Proof.
  intros * Hprefix Hhistory Htype Hkind Hrestore.
  unfold mutex_del_parent_prefix_ok in Hprefix; unfold mutex_del_api_program; rewrite Hprefix.
  left; exists acquired, kind, returned; repeat split; assumption || reflexivity.
Qed.

Lemma mutex_del_api_program_critical :
  forall environment critical sg original pe option eid before acquired checkpoint
    pointer code request returned after,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_owner_source_history sg before acquired ->
  mutex_del_parent_critical_observation sg eid option pointer code request acquired checkpoint ->
  mutex_api_tail_history environment critical sg original checkpoint request returned after ->
  mutex_del_api_program environment critical sg original pe option eid before (pointer, code) after.
Proof.
  intros * Hprefix Hhistory Hcritical Htail.
  unfold mutex_del_parent_prefix_ok in Hprefix; unfold mutex_del_api_program; rewrite Hprefix.
  right; exists acquired, checkpoint, request, returned; auto.
Qed.

Lemma mutex_del_api_safe_return :
  forall environment critical sg original pe option eid before pointer code after X,
  mutex_del_api_program environment critical sg original pe option eid before (pointer, code) after ->
  mutex_del_api_refinement_pre environment critical sg original pe option eid before X ->
  safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z pointer) X.
Proof.
  intros * Hsem Hexec.
  assert (Hatomic : hs_eval
    (atomic_cmd (mutex_del_api_program environment critical sg original pe option eid))
    (LastSeen before) (LastSeen after) (pointer, code)).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P HP.
    exists (RTrans_Abs after); split; [|intro state; split; trivial].
    exists before, after; split; [apply HP; exact I|].
    split; [exact Hsem|intro state; split; trivial]. }
  pose proof (highstepbind_derive _ _ _ (pointer, code) (LastSeen after) Hatomic X Hexec) as Hobs.
  eapply (highstependret_derive (mutex_del_api_observe_result (pointer, code))
    (LastSeen after) pointer (fun _ => LastSeen after)); [|exact Hobs].
  unfold hs_eval, LastSeen, mutex_del_api_observe_result; intros P HP.
  exists P; split; [split; reflexivity|exact HP].
Qed.

Lemma mutex_del_api_early_return_same_x :
  forall environment external platform critical saved_local sg original mask
    before pe option eid pointer error X,
  mutex_del_before_save_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) = Some (pointer, error) ->
  mutex_del_api_refinement_pre environment critical sg original pe option eid before X ->
  mutex_del_continuation_entry environment external platform saved_local sg original mask before |--
  mutex_del_api_return_post environment external platform critical saved_local sg original mask
    before pe option eid pointer (encode_os_err_code error) X.
Proof.
  intros * Herror Hsafe.
  assert (Hprogram : mutex_del_api_program environment critical sg original pe option eid
    before (pointer, encode_os_err_code error) before)
    by (apply mutex_del_api_program_early; assumption).
  assert (Hreturn : safeExec (LastSeen before)
    (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z pointer) X)
    by (eapply mutex_del_api_safe_return; eassumption).
  sep_apply_l_atomic (mutex_api_entry_return_at environment external platform saved_local
    sg original mask before).
  unfold mutex_del_api_return_post; Exists original before; entailer!.
Qed.

Lemma mutex_del_api_type_error_return_same_x :
  forall environment external platform critical saved_local sg original mask
    before pe option eid acquired kind X,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_owner_source_history sg before acquired ->
  mutex_del_runtime_type_observation sg eid acquired kind -> kind <> 4 ->
  mutex_del_api_refinement_pre environment critical sg original pe option eid before X ->
  mutex_api_restore_post environment external platform critical saved_local sg original mask acquired |--
  mutex_del_api_return_post environment external platform critical saved_local sg original mask
    before pe option eid pe (encode_os_err_code OS_ERR_EVENT_TYPE) X.
Proof.
  intros * Hprefix Hhistory Htype Hkind Hsafe.
  unfold mutex_api_restore_post; Intros returned after.
  assert (Hprogram : mutex_del_api_program environment critical sg original pe option eid
    before (pe, encode_os_err_code OS_ERR_EVENT_TYPE) after)
    by (eapply mutex_del_api_program_type_error; eassumption).
  assert (Hreturn : safeExec (LastSeen after)
    (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z pe) X)
    by (eapply mutex_del_api_safe_return; eassumption).
  unfold mutex_del_api_return_post; Exists returned after; entailer!.
Qed.

Lemma mutex_del_api_critical_return_same_x :
  forall environment external platform critical saved_local sg original mask
    before pe option eid acquired checkpoint pointer code request X,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_owner_source_history sg before acquired ->
  mutex_del_parent_critical_observation sg eid option pointer code request acquired checkpoint ->
  mutex_del_api_refinement_pre environment critical sg original pe option eid before X ->
  mutex_api_tail_post environment external platform critical saved_local
    sg original mask checkpoint request |--
  mutex_del_api_return_post environment external platform critical saved_local sg original mask
    before pe option eid pointer code X.
Proof.
  intros * Hprefix Hhistory Hcritical Hsafe.
  unfold mutex_api_tail_post; Intros returned after.
  assert (Hprogram : mutex_del_api_program environment critical sg original pe option eid
    before (pointer, code) after)
    by (eapply mutex_del_api_program_critical; eassumption).
  assert (Hreturn : safeExec (LastSeen after)
    (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z pointer) X)
    by (eapply mutex_del_api_safe_return; eassumption).
  unfold mutex_del_api_return_post; Exists returned after; entailer!.
Qed.
