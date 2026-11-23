Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reuse the already proved deletion effect: protected lookup, ready/event/
    flag removal, the completed-C-environment window, and exact recycling.
    Its phase rely is the existing explicit modular C contract, not an
    additional platform law. The final Restore still returns its real
    endpoint and context; the later Scheduler is a separate program. *)
Definition task_delete_protected_program environment critical sg requested name original :
  program UCOS2_Verify_State (Z * OsSchedCallContext) :=
  fun initial result final => exists cut_call cut,
    task_tcb_init_stack_same_call cut_call original /\
    task_delete_effect sg requested name initial (fst result) cut /\
    task_delete_restore_history environment critical requested TaskDeleteStable sg
      cut_call cut (snd result) final.

Definition task_delete_after_restore_program environment critical sg mask
  (result : Z * OsSchedCallContext) : program UCOS2_Verify_State Z :=
  if Z.eqb (fst result) 0 then
    StateRelMonad.bind (get' (fun s : UCOS2_Verify_State => s.(SchedState).(isRunning)))
      (fun running => if running then
        StateRelMonad.bind
          (os_sched_continuation_program environment critical sg (snd result) mask)
          (fun _ => StateRelMonad.ret 0)
        else StateRelMonad.ret 0)
  else StateRelMonad.ret (fst result).

Definition task_delete_program environment critical sg requested name original mask :
  program UCOS2_Verify_State Z :=
  StateRelMonad.bind (get' (fun s : UCOS2_Verify_State => s))
    (fun initial =>
      match task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested with
      | Some error => StateRelMonad.ret (encode_os_err_code error)
      | None => StateRelMonad.bind
          (task_delete_protected_program environment critical sg requested name original)
          (task_delete_after_restore_program environment critical sg mask)
      end).

Definition task_delete_safe environment critical sg requested name original mask initial
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun s => s = initial)
    (task_delete_program environment critical sg requested name original mask) X.

Definition task_delete_safe_result result final
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun s => s = final) (StateRelMonad.ret result) X.

Definition task_delete_sched_safe environment critical sg call mask before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun s => s = before)
    (StateRelMonad.bind (os_sched_continuation_program environment critical sg call mask)
      (fun _ => StateRelMonad.ret 0)) X.

(** The existing resource post and X share this very [final], not two
    independently chosen existential kernel states. The old relation is
    retained for existing consumers; the public program supplies the
    stronger ordered return/scheduling observation. *)
Definition task_delete_api_post environment critical saved_local sg requested name
  original mask initial result (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX cut_call returned final deletion_cut loan,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_same_call cut_call original /\
      task_delete_effect sg requested name initial result deletion_cut /\
      task_delete_return_relation environment critical requested sg cut_call deletion_cut returned final /\
      task_delete_safe_result result final X) &&
    task_delete_call_closed environment saved_local TaskDeleteStable loan sg returned mask final.

Definition task_delete_sched_history_return_with_loan environment critical saved_local sg
  original mask before loan : Assertion :=
  os_sched_continuation_history_return_post environment critical saved_local kernel_program_inv
    sg original mask before ** task_delete_return_loan sg loan.

Lemma task_delete_api_post_weaken :
  forall environment critical saved_local sg requested name original mask initial result X,
  task_delete_api_post environment critical saved_local sg requested name original mask initial result X |--
  task_delete_post environment critical saved_local sg requested name original mask initial result.
Proof.
  intros; unfold task_delete_api_post; Intros cut_call returned final cut loan.
  unfold task_delete_post; Exists cut_call returned final cut loan; entailer!.
Qed.

Lemma task_delete_prefix_error_nonzero : forall sg nesting requested error,
  task_delete_prefix_error sg false nesting requested = Some error ->
  encode_os_err_code error <> 0.
Proof.
  intros sg nesting requested error Herror.
  unfold task_delete_prefix_error in Herror; rewrite andb_false_r in Herror.
  destruct (0 <? nesting); [inversion Herror; discriminate|].
  destruct (requested =? osTaskIdlePrio sg); [inversion Herror; discriminate|].
  destruct ((cfgArgumentChecks (osKernelConfig sg) && (osLowestPrio sg <=? requested) &&
    negb (requested =? osPrioSelf sg))%bool); inversion Herror; discriminate.
Qed.

Lemma task_delete_success_prefix : forall sg requested name initial cut,
  task_delete_effect sg requested name initial 0 cut ->
  task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = None.
Proof.
  intros sg requested name initial cut Heffect; inversion Heffect; subst; try assumption.
  exfalso; eapply task_delete_prefix_error_nonzero; eassumption || reflexivity.
Qed.

Lemma task_delete_prefix_error_program :
  forall environment critical sg requested name original mask initial error,
  task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = Some error ->
  task_delete_program environment critical sg requested name original mask
    initial (encode_os_err_code error) initial.
Proof.
  intros; unfold task_delete_program; exists initial, initial.
  split; [split; reflexivity|]. rewrite H; split; reflexivity.
Qed.

Lemma task_delete_program_safe_return :
  forall environment critical sg requested name original mask initial result final X,
  task_delete_program environment critical sg requested name original mask initial result final ->
  task_delete_safe environment critical sg requested name original mask initial X ->
  task_delete_safe_result result final X.
Proof.
  intros environment critical sg requested name original mask initial result final X Hstep Hsafe.
  unfold task_delete_safe_result, task_delete_safe in *.
  eapply (highstependret_derive
    (task_delete_program environment critical sg requested name original mask)
    (fun s => s = initial) result (fun _ s => s = final)).
  - intros s ->; exists final; auto.
  - exact Hsafe.
Qed.

Lemma task_delete_safe_protected_continuation :
  forall environment critical sg requested name original mask initial result returned current X,
  task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = None ->
  task_delete_protected_program environment critical sg requested name original
    initial (result, returned) current ->
  task_delete_safe environment critical sg requested name original mask initial X ->
  safeExec (fun s => s = current)
    (task_delete_after_restore_program environment critical sg mask (result, returned)) X.
Proof.
  intros environment critical sg requested name original mask initial result returned current X
    Hprefix Hstep Hsafe.
  unfold task_delete_safe, task_delete_program in Hsafe.
  eapply safeExec_get'_bind with (a := initial) in Hsafe;
    [|intros s ->; reflexivity].
  rewrite Hprefix in Hsafe.
  eapply (highstepbind_derive
    (task_delete_protected_program environment critical sg requested name original)
    (task_delete_after_restore_program environment critical sg mask)
    (fun s => s = initial) (result, returned) (fun s => s = current)).
  - intros s ->; exists current; auto.
  - exact Hsafe.
Qed.

Lemma task_delete_final_body_sched_safe :
  forall environment critical sg requested name original mask initial cut_call cut returned current X,
  task_delete_result_history sg requested name original initial cut_call cut ->
  task_delete_restore_history environment critical requested TaskDeleteStable sg cut_call cut returned current ->
  current.(SchedState).(isRunning) = true ->
  task_delete_safe environment critical sg requested name original mask initial X ->
  task_delete_sched_safe environment critical sg returned mask current X.
Proof.
  intros environment critical sg requested name original mask initial cut_call cut returned current X
    [Hsame [Heffect Hprotocol]] Hrestore Hrunning Hsafe.
  assert (Hstep : task_delete_protected_program environment critical sg requested name original
    initial (0, returned) current).
  { exists cut_call, cut; auto. }
  pose proof (task_delete_safe_protected_continuation environment critical sg requested name
    original mask initial 0 returned current X
    (task_delete_success_prefix sg requested name initial cut Heffect) Hstep Hsafe) as Htail.
  unfold task_delete_after_restore_program in Htail; cbn [fst snd Z.eqb] in Htail.
  eapply safeExec_get'_bind with (a := true) in Htail.
  - exact Htail.
  - intros s ->; symmetry; exact Hrunning.
Qed.

Lemma task_delete_prefix_error_api_post :
  forall environment critical saved_local completed sg requested name call mask initial error X,
  task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = Some error ->
  task_delete_safe environment critical sg requested name call mask initial X ->
  task_delete_entry environment critical saved_local completed sg requested call mask initial |--
  task_delete_api_post environment critical saved_local sg requested name call mask initial
    (encode_os_err_code error) X.
Proof.
  intros environment critical saved_local completed sg requested name call mask initial error X
    Herror Hsafe.
  pose proof (task_delete_program_safe_return environment critical sg requested name call mask
    initial (encode_os_err_code error) initial X
    (task_delete_prefix_error_program environment critical sg requested name call mask initial error Herror)
    Hsafe) as Hreturn.
  unfold task_delete_entry, task_delete_api_post; Intros.
  Exists call call initial initial (@None FlagWaiterState).
  assert (Hsame : task_tcb_init_stack_same_call call call)
    by (unfold task_tcb_init_stack_same_call; auto).
  assert (Heffect : task_delete_effect sg requested name initial (encode_os_err_code error) initial)
    by (apply TaskDeletePrefixError; exact Herror).
  assert (Htail : task_delete_return_relation environment critical requested sg call initial call initial)
    by constructor.
  entailer!.
Qed.

Lemma task_delete_lookup_error_api_post :
  forall environment critical saved_local sg requested name original mask initial
    current acquired selected error X,
  task_delete_lookup_history sg requested original initial current acquired ->
  task_delete_selection sg requested acquired.(TskState) acquired.(SchedState) selected ->
  task_delete_table_lookup acquired.(TskState) selected (inl error) ->
  encode_os_err_code error <> 0 ->
  task_delete_safe environment critical sg requested name original mask initial X ->
  task_delete_restore_post environment critical saved_local requested TaskDeleteStable None
    sg current mask acquired |--
  task_delete_api_post environment critical saved_local sg requested name original mask initial
    (encode_os_err_code error) X.
Proof.
  intros environment critical saved_local sg requested name original mask initial
    current acquired selected error X
    [Hstatic [Hbound [Hsame [Hprefix [Hrely Hprotocol]]]]] Hselection Hlookup Hnonzero Hsafe.
  unfold task_delete_restore_post; Intros returned final.
  assert (Hrestore : task_delete_restore_history environment critical requested TaskDeleteStable
    sg current acquired returned final) by (unfold task_delete_restore_history; tauto).
  assert (Heffect : task_delete_effect sg requested name initial (encode_os_err_code error) acquired)
    by (eapply TaskDeleteLookupError; eassumption).
  assert (Hstep : task_delete_protected_program environment critical sg requested name original
    initial (encode_os_err_code error, returned) final).
  { exists current, acquired; auto. }
  pose proof (task_delete_safe_protected_continuation environment critical sg requested name original
    mask initial (encode_os_err_code error) returned final X Hprefix Hstep Hsafe) as Hreturn.
  unfold task_delete_after_restore_program in Hreturn; cbn [fst snd] in Hreturn.
  rewrite (proj2 (Z.eqb_neq _ _) Hnonzero) in Hreturn.
  assert (Hsame_return : task_tcb_init_stack_same_call returned original).
  { destruct Hrestore as [_ [[[Hi [Ho Hs]] Havailable] _]], Hsame as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Htail : task_delete_return_relation environment critical requested sg current acquired returned final)
    by (apply TaskDeleteReturnRestored; tauto).
  unfold task_delete_api_post; Exists current returned final acquired (@None FlagWaiterState).
  entailer!.
Qed.

Lemma task_delete_final_body_api_post :
  forall environment critical saved_local sg requested name original mask initial returned final cut loan X,
  task_delete_running final <> 1 ->
  task_delete_safe environment critical sg requested name original mask initial X ->
  task_delete_final_body environment critical saved_local sg requested name original mask initial
    returned final cut loan |--
  task_delete_api_post environment critical saved_local sg requested name original mask initial 0 X.
Proof.
  intros environment critical saved_local sg requested name original mask initial returned final cut loan X
    Hstopped Hsafe.
  unfold task_delete_final_body; Intros.
  assert (Hhistory : exists cut_call,
    task_delete_result_history sg requested name original initial cut_call cut /\
    task_delete_restore_history environment critical requested TaskDeleteStable sg cut_call cut returned final)
    by tauto.
  destruct Hhistory as [cut_call [[Hcut_same [Heffect Hprotocol]] Hrestore]].
  assert (Hstep : task_delete_protected_program environment critical sg requested name original
    initial (0, returned) final) by (exists cut_call, cut; auto).
  pose proof (task_delete_safe_protected_continuation environment critical sg requested name original
    mask initial 0 returned final X
    (task_delete_success_prefix sg requested name initial cut Heffect) Hstep Hsafe) as Hreturn.
  unfold task_delete_after_restore_program in Hreturn; cbn [fst snd Z.eqb] in Hreturn.
  assert (Hrunning : final.(SchedState).(isRunning) = false).
  { unfold task_delete_running in Hstopped; destruct final.(SchedState).(isRunning); congruence. }
  eapply safeExec_get'_bind with (a := false) in Hreturn;
    [|intros s ->; symmetry; exact Hrunning].
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { destruct Hrestore as [_ [[[Hi [Ho Hs]] Havailable] _]], Hcut_same as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Htail : task_delete_return_relation environment critical requested sg cut_call cut returned final).
  { destruct Hrestore as [Htrace [Hnormal [HR Htransport]]].
    apply TaskDeleteReturnRestored; assumption. }
  unfold task_delete_api_post; Exists cut_call returned final cut loan; entailer!.
Qed.

Lemma task_delete_scheduled_api_post :
  forall environment critical saved_local sg requested name original mask initial
    cut_call cut middle current loan X,
  task_delete_result_history sg requested name original initial cut_call cut ->
  task_delete_restore_history environment critical requested TaskDeleteStable sg cut_call cut middle current ->
  current.(SchedState).(isRunning) = true ->
  task_delete_sched_safe environment critical sg middle mask current X ->
  task_delete_sched_history_return_with_loan environment critical saved_local sg middle mask current loan |--
  task_delete_api_post environment critical saved_local sg requested name original mask initial 0 X.
Proof.
  intros environment critical saved_local sg requested name original mask initial cut_call cut
    middle current loan X [Hcut_same [Heffect Hprotocol]]
    [Htrace [Hnormal [HR Htransport]]] Hrunning Hsafe.
  unfold task_delete_sched_history_return_with_loan, os_sched_continuation_history_return_post.
  Intros returned final.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg middle mask current returned final)
    by tauto.
  assert (Hreturn : task_delete_safe_result 0 final X).
  { unfold task_delete_safe_result, task_delete_sched_safe in *.
    eapply (highstependret_derive
      (StateRelMonad.bind (os_sched_continuation_program environment critical sg middle mask)
        (fun _ => StateRelMonad.ret 0))
      (fun s => s = current) 0 (fun _ s => s = final)).
    - intros s ->; exists final; split; [|reflexivity].
      exists returned, final; split.
      + apply os_sched_continuation_program_iff; exact Hhistory.
      + split; reflexivity.
    - exact Hsafe. }
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { assert (Hlast : task_tcb_init_stack_same_call returned middle) by tauto.
    destruct Hlast as [Hi [Ho Hs]], Hnormal as [[Hi' [Ho' Hs']] Havailable],
      Hcut_same as [Hi'' [Ho'' Hs'']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Htail : task_delete_return_relation environment critical requested sg cut_call cut returned final).
  { eapply TaskDeleteReturnScheduled; eassumption || tauto. }
  unfold task_delete_api_post; Exists cut_call returned final cut loan.
  rewrite task_delete_call_closed_stable_split_loan.
  unfold os_sched_continuation_pre; entailer!.
Qed.

(** The old internal call contract is a conservative instance: use this
    universally available postcondition and [task_delete_api_post_weaken].
    The public API and its C witnesses still quantify over the same arbitrary X. *)
Lemma task_delete_safe_true :
  forall environment critical sg requested name original mask initial,
  task_delete_safe environment critical sg requested name original mask initial
    (fun _ _ => True).
Proof.
  intros; unfold task_delete_safe, safeExec, safe.
  exists initial; split; [reflexivity |].
  intros result final Hstep; exact I.
Qed.
