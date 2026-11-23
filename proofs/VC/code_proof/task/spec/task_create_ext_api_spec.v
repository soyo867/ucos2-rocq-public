Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.VC.code.task.spec.task_create_ext_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_api_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The common creation program is instantiated with Extended arguments and
    the exact post-clear lower/upper images. OS_TaskStkClr changes only the
    separately owned child buffer; its checked C contract and reversible
    split/merge retain those bytes below. The monadic observation is the
    real error byte and kernel state, not the private caller heap. *)
Definition task_create_ext_api_post environment critical saved_local sg region args task_return
  lower old_frame upper prefix middle suffix original mask result
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
      (result = 0 \/ result = 40 \/ result = 42 \/ result = 60 \/ result = 66) /\
      (result = 42 -> 63 < args.(createPriority)) /\
      (result <> 42 -> args.(createPriority) <= 63) /\
      task_create_safe current (StateRelMonad.ret result) X) &&
    (task_create_continuation_input environment critical saved_local sg returned mask current **
     unmap_table_rep sg **
     (if Z.eq_dec result 0 then emp else
       task_stack_storage region
         (if Z.eq_dec result 66 then
           task_create_stack_image TaskStackNoVFP args task_return
             (task_create_ext_after_lower args lower old_frame upper prefix middle suffix)
             (task_create_ext_after_upper args lower old_frame upper prefix middle suffix)
          else lower ++ old_frame ++ upper))).

Lemma task_create_ext_api_post_weaken : forall environment critical saved_local sg region args
  task_return lower old_frame upper prefix middle suffix original mask result X,
  task_create_ext_api_post environment critical saved_local sg region args task_return
    lower old_frame upper prefix middle suffix original mask result X |--
  task_create_ext_post environment critical saved_local sg region args task_return
    lower old_frame upper prefix middle suffix original mask result.
Proof.
  intros; unfold task_create_ext_api_post; Intros returned current.
  unfold task_create_ext_post; Exists returned current; entailer!; tauto.
Qed.

Lemma task_create_ext_success_api_post : forall environment critical saved_local sg region args
  task_return lower old_frame upper prefix middle suffix original mask X,
  args.(createPriority) <= 63 ->
  task_create_api_post environment critical saved_local sg region args task_return
    lower old_frame upper original mask 0 X |--
  task_create_ext_api_post environment critical saved_local sg region args task_return
    lower old_frame upper prefix middle suffix original mask 0 X.
Proof.
  intros; unfold task_create_api_post; Intros returned current.
  unfold task_create_ext_api_post; Exists returned current.
  destruct (Z.eq_dec 0 0); [|contradiction]; entailer!; try tauto; lia.
Qed.

Lemma task_create_ext_schedule_safe_return : forall environment critical saved_local sg original
  mask X region args task_return lower old_frame upper prefix middle suffix,
  args.(createPriority) <= 63 ->
  task_create_schedule_post environment critical saved_local sg original mask X |--
  task_create_ext_api_post environment critical saved_local sg region args task_return
    lower old_frame upper prefix middle suffix original mask 0 X.
Proof.
  intros.
  sep_apply_l_atomic (task_create_schedule_safe_return environment critical saved_local sg original
    mask X region args task_return lower old_frame upper).
  apply task_create_ext_success_api_post; assumption.
Qed.

Lemma task_create_ext_restore_safe_return : forall environment critical saved_local sg region args
  task_return lower old_frame upper prefix middle suffix original actual mask saved released
  result X,
  args.(createPriority) <= 63 ->
  task_tcb_init_stack_same_call actual original -> interrupt_saved_value mask saved ->
  (result = 40 \/ result = 60 \/ result = 66) ->
  task_create_safe released (task_create_restore_return_program environment critical sg actual result) X ->
  task_tcb_init_modular_restore_output environment critical saved_local sg actual saved released **
    unmap_table_rep sg **
    task_stack_storage region
      (if Z.eq_dec result 66 then
        task_create_stack_image TaskStackNoVFP args task_return
          (task_create_ext_after_lower args lower old_frame upper prefix middle suffix)
          (task_create_ext_after_upper args lower old_frame upper prefix middle suffix)
       else lower ++ old_frame ++ upper) |--
  task_create_ext_api_post environment critical saved_local sg region args task_return
    lower old_frame upper prefix middle suffix original mask result X.
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    prefix middle suffix original actual mask saved released result X Hpriority Hsame Hsaved Hcode Hsafe.
  sep_apply_l_atomic (task_create_restore_safe_observation environment critical saved_local sg
    actual saved released _ X Hsafe); Intros returned current.
  assert (Hreturned : task_tcb_init_stack_same_call returned original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; Intros.
  unfold task_create_ext_api_post; Exists returned current.
  destruct (Z.eq_dec result 0); [lia|].
  unfold task_create_continuation_input; rewrite (proj2 Hsaved); entailer!; try tauto; lia.
Qed.
