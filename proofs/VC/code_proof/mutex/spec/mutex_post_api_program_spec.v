Require Import Coq.ZArith.ZArith.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_continuation_spec.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The initial error order and protected operation are unchanged. The
    final world comes from the actual Restore and, only on the scheduled
    branch, the subsequent Scheduler call. No current ECB lifetime is
    inferred from the historical protected snapshot. *)
Definition mutex_post_api_program environment critical sg original pe eid observed
  : program UCOS2_Verify_State Z :=
  fun before code after =>
    match mutex_post_before_save_error pe (event_slot_type_value before.(EventState) eid)
      before.(IntrState).(intNesting) with
    | Some error => code = encode_os_err_code error /\ after = before
    | None => exists acquired current caller node result scheduled committed returned,
        critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
        mutex_query_lookup acquired eid current /\ current.(eventType) = OS_EVENT_TYPE_MUTEX /\
        current.(eventGeneration) = observed.(eventGeneration) /\
        mutex_post_native_caller sg original.(os_sched_call_invocation)
          original.(os_sched_call_origin) acquired original caller node /\
        mutex_post_critical sg eid caller acquired result scheduled committed /\
        code = encode_os_err_code result /\
        mutex_api_tail_history environment critical sg original committed
          (if scheduled then 1 else 0) returned after
    end.

Definition mutex_post_api_refinement_pre environment critical sg original pe eid observed before X : Prop :=
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_post_api_program environment critical sg original pe eid observed))
      sem_query_observe_error) X.

Definition mutex_post_api_return_post environment external platform critical saved_local
  sg original mask pe before eid observed code X : Assertion :=
  EX returned after,
    coq_prop (mutex_post_api_program environment critical sg original pe eid observed before code after /\
      safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z code) X) &&
    mutex_del_continuation_return_at environment external platform saved_local
      sg original mask returned after.

Lemma mutex_post_api_program_early :
  forall environment critical sg original pe eid observed before error,
  mutex_post_before_save_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) = Some error ->
  mutex_post_api_program environment critical sg original pe eid observed
    before (encode_os_err_code error) before.
Proof. intros; unfold mutex_post_api_program; rewrite H; auto. Qed.

Lemma mutex_post_api_program_critical :
  forall environment critical sg original pe eid observed before acquired current caller node
    result scheduled committed returned after,
  mutex_post_api_prefix pe before eid ->
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired ->
  mutex_query_lookup acquired eid current -> current.(eventType) = OS_EVENT_TYPE_MUTEX ->
  current.(eventGeneration) = observed.(eventGeneration) ->
  mutex_post_native_caller sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
    acquired original caller node ->
  mutex_post_critical sg eid caller acquired result scheduled committed ->
  mutex_api_tail_history environment critical sg original committed
    (if scheduled then 1 else 0) returned after ->
  mutex_post_api_program environment critical sg original pe eid observed
    before (encode_os_err_code result) after.
Proof.
  intros * Hprefix Hinterval Hlookup Htype Hgeneration Hcaller Hcritical Htail.
  unfold mutex_post_api_prefix in Hprefix.
  unfold mutex_post_api_program; rewrite Hprefix.
  exists acquired, current, caller, node, result, scheduled, committed, returned.
  exact (conj Hinterval (conj Hlookup (conj Htype (conj Hgeneration
    (conj Hcaller (conj Hcritical (conj eq_refl Htail))))))).
Qed.

Lemma mutex_post_api_safe_return :
  forall environment critical sg original pe eid observed before code after X,
  mutex_post_api_program environment critical sg original pe eid observed before code after ->
  mutex_post_api_refinement_pre environment critical sg original pe eid observed before X ->
  safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z code) X.
Proof.
  intros * Hsem Hexec.
  assert (Hatomic : hs_eval
    (atomic_cmd (mutex_post_api_program environment critical sg original pe eid observed))
    (LastSeen before) (LastSeen after) code).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P HP.
    exists (RTrans_Abs after); split; [|intro state; split; trivial].
    exists before, after; split; [apply HP; exact I|].
    split; [exact Hsem|intro state; split; trivial]. }
  pose proof (highstepbind_derive _ _ _ code (LastSeen after) Hatomic X Hexec) as Hobs.
  eapply (highstependret_derive (sem_query_observe_error code) (LastSeen after) code
    (fun _ => LastSeen after)); [|exact Hobs].
  unfold hs_eval, LastSeen; intros P HP; exists P; split; [split; reflexivity|exact HP].
Qed.

Lemma mutex_post_api_early_return_same_x :
  forall environment external platform critical saved_local sg original mask pe before eid observed error X,
  mutex_post_before_save_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) = Some error ->
  mutex_post_api_refinement_pre environment critical sg original pe eid observed before X ->
  mutex_del_continuation_entry environment external platform saved_local sg original mask before |--
  mutex_post_api_return_post environment external platform critical saved_local
    sg original mask pe before eid observed (encode_os_err_code error) X.
Proof.
  intros * Herror Hsafe.
  pose proof (mutex_post_api_program_early environment critical sg original pe
    eid observed before error Herror) as Hprogram.
  pose proof (mutex_post_api_safe_return environment critical sg original pe
    eid observed before (encode_os_err_code error) before X Hprogram Hsafe) as Hreturn.
  sep_apply_l_atomic (mutex_api_entry_return_at environment external platform saved_local
    sg original mask before).
  unfold mutex_post_api_return_post; Exists original before; entailer!.
Qed.

Lemma mutex_post_api_critical_return_same_x :
  forall environment external platform critical saved_local sg original mask pe before eid observed
    acquired current caller node result scheduled committed X,
  mutex_post_api_prefix pe before eid ->
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired ->
  mutex_query_lookup acquired eid current -> current.(eventType) = OS_EVENT_TYPE_MUTEX ->
  current.(eventGeneration) = observed.(eventGeneration) ->
  mutex_post_native_caller sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
    acquired original caller node ->
  mutex_post_critical sg eid caller acquired result scheduled committed ->
  mutex_post_api_refinement_pre environment critical sg original pe eid observed before X ->
  mutex_api_tail_post environment external platform critical saved_local sg original mask committed
    (if scheduled then 1 else 0) |--
  mutex_post_api_return_post environment external platform critical saved_local
    sg original mask pe before eid observed (encode_os_err_code result) X.
Proof.
  intros * Hprefix Hinterval Hlookup Htype Hgeneration Hcaller Hcritical Hsafe.
  unfold mutex_api_tail_post; Intros returned after.
  assert (Hprogram : mutex_post_api_program environment critical sg original pe eid observed
    before (encode_os_err_code result) after).
  { eapply mutex_post_api_program_critical; eassumption. }
  pose proof (mutex_post_api_safe_return environment critical sg original pe
    eid observed before (encode_os_err_code result) after X Hprogram Hsafe) as Hreturn.
  unfold mutex_post_api_return_post; Exists returned after; entailer!.
Qed.
