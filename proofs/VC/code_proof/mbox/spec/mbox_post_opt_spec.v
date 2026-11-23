Require Export Ucos2Verify.VC.code.mbox.spec.mbox_post_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.error_codes.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Only BROADCAST (1) and NO_SCHED (4) are observed. Other INT8U bits
    remain legal and do not alter the mailbox operation. Application message
    data remains an external frame: the Event owns only its pointer cell. *)
Definition mbox_post_opt_broadcast sg eid message :=
  event_broadcast sg eid PendMbox message PendOK.

Definition mbox_post_opt_schedule_flag (options : Z) : Z :=
  if Z.eqb (Z.land options 4) 0 then 1 else 0.

Definition mbox_post_opt_critical (sg : StableGlobVars) (eid : EventID)
  (message : addr) (options : Z) : program UCOS2_Verify_State (Z * bool) :=
  fun acquired result released =>
    exists node, q_post_lookup acquired eid node /\
      if Z.eqb (q_post_group acquired node) 0 then
        exists m, node.(mboxFields) = Some m /\
          if Z.eqb (mbox_message_ptr m) 0
          then result = (0, false) /\ released = mbox_post_store_state acquired eid node message
          else result = (20, false) /\ released = acquired
      else result = (0, Z.eqb (Z.land options 4) 0) /\
        if Z.eqb (Z.land options 1) 0
        then exists priority, event_task_rdy sg acquired eid PendMbox message PendOK =
          Some (priority, released)
        else exists priorities, mbox_post_opt_broadcast sg eid message acquired priorities released.

Lemma mbox_post_opt_wake_decompose : forall sg s eid e message priority after,
  UCOS2_state_inv sg s -> q_post_lookup s eid e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX -> q_post_group s e <> 0 ->
  mbox_post_wake_result sg eid message s after priority ->
  exists head tail old,
    e.(waitList) = head :: tail /\ s.(TskState).(inUsedTaskStates) head = Some old /\
    priority = old.(curPrio) /\
    after = event_wake_state sg s eid e head old PendMbox message PendOK /\
    UCOS2_state_inv sg after /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list e tail).
Proof.
  intros sg s eid e message priority after Hvalid He Htype Hgroup Hstep.
  eapply event_wake_decompose; try eassumption.
  rewrite Htype; reflexivity.
Qed.

Lemma mbox_post_opt_single_wake_critical : forall sg entry eid current message options priority after,
  q_post_lookup entry eid current -> q_post_group entry current <> 0 ->
  Z.land options 1 = 0 -> mbox_post_wake_result sg eid message entry after priority ->
  mbox_post_opt_critical sg eid message options entry
    (0, Z.eqb (Z.land options 4) 0) after.
Proof.
  intros sg entry eid current message options priority after Hlookup Hgroup Hsingle Hstep.
  exists current; split; [exact Hlookup|].
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup); split; [reflexivity|].
  rewrite Hsingle; cbn; exists priority; exact Hstep.
Qed.

Lemma mbox_post_opt_broadcast_critical : forall sg entry eid current message options priorities after,
  q_post_lookup entry eid current -> q_post_group entry current <> 0 ->
  Z.land options 1 <> 0 -> mbox_post_opt_broadcast sg eid message entry priorities after ->
  mbox_post_opt_critical sg eid message options entry
    (0, Z.eqb (Z.land options 4) 0) after.
Proof.
  intros sg entry eid current message options priorities after Hlookup Hgroup Hbroadcast Hloop.
  exists current; split; [exact Hlookup|].
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup); split; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) Hbroadcast); exists priorities; exact Hloop.
Qed.

Lemma mbox_post_opt_full_critical : forall sg entry eid current m message options,
  q_post_lookup entry eid current -> current.(mboxFields) = Some m ->
  q_post_group entry current = 0 -> mbox_message_ptr m <> 0 ->
  mbox_post_opt_critical sg eid message options entry (20, false) entry.
Proof.
  intros; exists current; split; [exact H|]; rewrite H1.
  exists m; split; [exact H0|]; rewrite (proj2 (Z.eqb_neq _ _) H2); auto.
Qed.

Lemma mbox_post_opt_store_critical : forall sg entry eid current m message options,
  q_post_lookup entry eid current -> current.(mboxFields) = Some m ->
  q_post_group entry current = 0 -> mbox_message_ptr m = 0 ->
  mbox_post_opt_critical sg eid message options entry (0, false)
    (mbox_post_store_state entry eid current message).
Proof.
  intros; exists current; split; [exact H|]; rewrite H1.
  exists m; split; [exact H0|]; rewrite H2; cbn; auto.
Qed.

Lemma mbox_post_opt_critical_has_result : forall sg state eid node message options,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> message <> 0 ->
  exists result after, mbox_post_opt_critical sg eid message options state result after.
Proof.
  intros sg state eid node message options Hvalid Hnode Htype Hmessage.
  destruct (Z.eq_dec (q_post_group state node) 0) as [Hempty|Hnonempty].
  - destruct (mbox_post_current_message sg state eid node Hvalid Hnode Htype Hempty)
      as [m [Hm [Hwait Hconsistent]]].
    destruct (Z.eq_dec (mbox_message_ptr m) 0) as [Hzero|Hfull].
    + exists (0, false), (mbox_post_store_state state eid node message).
      eapply mbox_post_opt_store_critical; eassumption.
    + exists (20, false), state.
      eapply mbox_post_opt_full_critical; eassumption.
  - destruct (Z.eq_dec (Z.land options 1) 0) as [Hsingle|Hbroadcast].
    + destruct node.(waitList) as [|head tail] eqn:Hlist;
        [contradiction Hnonempty; unfold q_post_group; rewrite Hlist; reflexivity|].
      destruct (mbox_post_wake_head sg state eid node head tail message Hvalid Hnode Htype Hlist)
        as [old [Hold [Hstep Hrest]]].
      exists (0, Z.eqb (Z.land options 4) 0),
        (event_wake_state sg state eid node head old PendMbox message PendOK).
      eapply mbox_post_opt_single_wake_critical; eassumption.
    + destruct (event_broadcast_exists node.(waitList) sg state eid node PendMbox message PendOK
        Hvalid Hnode ltac:(rewrite Htype; reflexivity) eq_refl)
        as [priorities [after [Hloop Hrest]]].
      exists (0, Z.eqb (Z.land options 4) 0), after.
      eapply mbox_post_opt_broadcast_critical; eassumption.
Qed.

Lemma mbox_post_opt_critical_preserves_validity : forall sg state eid node message options result after,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> message <> 0 ->
  mbox_post_opt_critical sg eid message options state result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg state eid node message options result after Hvalid Hnode Htype Hmessage
    [actual [Hactual Hstep]].
  assert (actual = node) by congruence; subst actual.
  destruct (Z.eqb (q_post_group state node) 0) eqn:Hgroup.
  - apply Z.eqb_eq in Hgroup.
    destruct Hstep as [m [Hm Hstep]].
    destruct (Z.eqb (mbox_message_ptr m) 0); destruct Hstep as [_ ->]; [|exact Hvalid].
    destruct (mbox_post_current_message sg state eid node Hvalid Hnode Htype Hgroup)
      as [fields [Hfields [Hempty Hconsistent]]].
    eapply mbox_post_store_preserves_validity; eassumption.
  - apply Z.eqb_neq in Hgroup; destruct Hstep as [_ Hstep].
    destruct (Z.eqb (Z.land options 1) 0).
    + destruct Hstep as [priority Hcall].
      destruct (mbox_post_opt_wake_decompose sg state eid node message priority after
        Hvalid Hnode Htype Hgroup Hcall) as [tid [tail [old [Hl [Ht [Hp [Ha [Hv Hn]]]]]]]].
      exact Hv.
    + destruct Hstep as [priorities Hloop].
      exact (proj1 (event_broadcast_result sg state eid node PendMbox message PendOK priorities after
        Hvalid Hnode ltac:(rewrite Htype; reflexivity) Hloop)).
Qed.

Definition mbox_post_opt_prefix_program environment critical sg caller mask pe eid message options
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = ((4, false), caller) /\ restored = before
    else if Z.eqb message 0 then result = ((3, false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 1 then
      exists active saved acquired error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        mbox_post_opt_critical sg eid message options acquired (error, schedule) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = ((error, schedule), returned)
    else result = ((1, false), caller) /\ restored = before.

(** The shared tail is exactly Restore's optional Scheduler continuation;
    it contains neither Queue storage nor an OSRunning guard. *)
Definition mbox_post_opt_program environment critical sg caller mask pe eid message options
  : program UCOS2_Verify_State Z :=
  bind (mbox_post_opt_prefix_program environment critical sg caller mask pe eid message options)
    (q_post_tail environment critical sg mask).

Definition mbox_post_opt_safe environment critical sg caller mask pe eid message options before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (mbox_post_opt_program environment critical sg caller mask pe eid message options) X.

Definition mbox_post_opt_caller_result environment critical sg original mask pe eid message options before
  error returned current : Prop :=
  exists prefix_caller restored schedule,
    mbox_post_opt_prefix_program environment critical sg original mask pe eid message options before
      ((error, schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

(** The separated coq_prop preserves its TT residual. The same existential
    witnesses index the actual return relation, arbitrary X, and all resources. *)
Definition mbox_post_opt_post environment critical saved_local sg original mask pe eid message options before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (mbox_post_opt_caller_result environment critical sg original mask pe eid message options before error returned current /\
      q_post_return_safe current error X) **
    q_post_closed environment critical saved_local sg returned mask current.

Lemma mbox_post_opt_program_null : forall environment critical sg caller mask eid message options before,
  mbox_post_opt_program environment critical sg caller mask 0 eid message options before 4 before.
Proof.
  intros; exists ((4, false), caller), before; split.
  - unfold mbox_post_opt_prefix_program; cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma mbox_post_opt_program_wrong_type : forall environment critical sg caller mask pe eid message options before,
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid <> 1 ->
  mbox_post_opt_program environment critical sg caller mask pe eid message options before 1 before.
Proof.
  intros; exists ((1, false), caller), before; split.
  - change (mbox_post_opt_prefix_program environment critical sg caller mask pe eid message options
      before ((1, false), caller) before).
    unfold mbox_post_opt_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H),
      (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1); split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma mbox_post_opt_prefix_protected : forall environment critical sg original active returned mask
  pe eid message options before acquired released restored saved error schedule,
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid = 1 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  mbox_post_opt_critical sg eid message options acquired (error, schedule) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  mbox_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, schedule), returned) restored.
Proof.
  intros; unfold mbox_post_opt_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0), H1; cbn.
  exists active, saved, acquired, error, schedule, released, returned; auto.
Qed.

Lemma mbox_post_opt_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid message options before restored error schedule X,
  mbox_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, schedule), returned) restored ->
  mbox_post_opt_safe environment critical sg original mask pe eid message options before X ->
  safeExec (fun state => state = restored)
    (q_post_tail environment critical sg mask ((error, schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid message options before restored error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (mbox_post_opt_prefix_program environment critical sg original mask pe eid message options)
    (q_post_tail environment critical sg mask) (fun state => state = before)
    ((error, schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma mbox_post_opt_program_nonschedule : forall environment critical sg original returned mask
  pe eid message options before restored error,
  mbox_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, false), returned) restored ->
  mbox_post_opt_program environment critical sg original mask pe eid message options before error restored.
Proof.
  intros; exists ((error, false), returned), restored; split; [assumption|].
  cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma mbox_post_opt_program_schedule : forall environment critical sg original returned final mask
  pe eid message options before restored current error,
  mbox_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, true), returned) restored ->
  task_resume_schedule_program environment critical sg returned mask restored final current ->
  mbox_post_opt_program environment critical sg original mask pe eid message options before error current.
Proof.
  intros; exists ((error, true), returned), restored; split; [assumption|].
  cbn [q_post_tail]; exists tt, current; split; [|split; reflexivity].
  exists final, current; split; [assumption|split; reflexivity].
Qed.

Lemma mbox_post_opt_safe_return : forall environment critical sg caller mask pe eid message options before current error X,
  mbox_post_opt_program environment critical sg caller mask pe eid message options before error current ->
  mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ->
  q_post_return_safe current error X.
Proof.
  intros environment critical sg caller mask pe eid message options before current error X Hprogram Hsafe.
  eapply (highstependret_derive
    (mbox_post_opt_program environment critical sg caller mask pe eid message options)
    (fun state => state = before) error (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma mbox_post_opt_closed_return : forall environment critical saved_local sg original returned mask
  pe eid message options before current error X,
  mbox_post_opt_caller_result environment critical sg original mask pe eid message options before error returned current ->
  mbox_post_opt_safe environment critical sg original mask pe eid message options before X ->
  q_post_closed environment critical saved_local sg returned mask current |--
  mbox_post_opt_post environment critical saved_local sg original mask pe eid message options before error X.
Proof.
  intros.
  assert (Hprogram : mbox_post_opt_program environment critical sg original mask pe eid message options before error current).
  { pose proof H as Hresult; destruct Hresult as [prefix_caller [restored [schedule [Hprefix Htail]]]].
    destruct schedule.
    - eapply mbox_post_opt_program_schedule with (final := returned); eassumption.
    - destruct Htail as [-> ->]; eapply mbox_post_opt_program_nonschedule; exact Hprefix. }
  pose proof (mbox_post_opt_safe_return _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0).
  unfold mbox_post_opt_post; Exists returned current; entailer!.
  apply derivable1_truep_intros.
Qed.

Lemma mbox_post_opt_program_null_message : forall environment critical sg caller mask pe eid options before,
  pe <> 0 -> mbox_post_opt_program environment critical sg caller mask pe eid 0 options before 3 before.
Proof.
  intros; exists ((3, false), caller), before; split.
  - unfold mbox_post_opt_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H); cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Definition mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before : Prop :=
  forall returned restored error,
    mbox_post_opt_prefix_program environment critical sg caller mask pe eid message options before
      ((error, true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Definition mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before
  (error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    mbox_post_opt_prefix_program environment critical sg caller mask pe eid message options before
      ((error, request), returned) current.

Definition mbox_post_opt_effect sg eid message options acquired (error schedule : Z) released : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    mbox_post_opt_critical sg eid message options acquired (error, request) released.

Definition mbox_post_opt_restore_pre environment critical saved_local sg caller active mask saved pe eid message options
  before acquired released error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ message <> 0 /\ event_slot_type_value before.(EventState) eid = 1 /\
    UCOS2_state_inv sg released /\ mbox_post_opt_effect sg eid message options acquired error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error schedule : Assertion :=
  EX returned current,
    coq_prop (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before
      error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma mbox_post_opt_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid message options
  before acquired released error schedule,
  mbox_post_opt_restore_pre environment critical saved_local sg caller active mask saved pe eid message options
    before acquired released error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold mbox_post_opt_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma mbox_post_opt_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid message options
  before acquired released error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid = 1 ->
  UCOS2_state_inv sg released -> mbox_post_opt_effect sg eid message options acquired error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid message options before acquired released error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Hmessage Htype Hvalid [request [-> Hstep]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before
    error (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply mbox_post_opt_prefix_protected;
      [exact Hpe|exact Hmessage|exact Htype|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold mbox_post_opt_restore_post; Exists returned current; entailer!.
Qed.

Lemma mbox_post_opt_nonschedule_return : forall environment critical saved_local sg caller mask pe eid message options before error X,
  mbox_post_opt_safe environment critical sg caller mask pe eid message options before X ->
  mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error 0 |--
  mbox_post_opt_post environment critical saved_local sg caller mask pe eid message options before error X.
Proof.
  intros; unfold mbox_post_opt_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; [discriminate|].
  assert (Hresult : mbox_post_opt_caller_result environment critical sg caller mask pe eid message options before error returned current).
  { exists returned, current, false; auto. }
  sep_apply_r_atomic (mbox_post_opt_closed_return environment critical saved_local sg caller returned mask pe eid message options before current error X Hresult H).
  entailer!.
Qed.

Lemma mbox_post_opt_restored_schedule_pre : forall environment critical saved_local sg caller mask pe eid message options before error,
  mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ->
  mbox_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error 1 |--
  EX returned current,
    coq_prop (mbox_post_opt_prefix_result environment critical sg caller mask pe eid message options before error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid message options before error Hprotocol.
  unfold mbox_post_opt_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]. pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current error Hprefix)).
  Exists returned current; entailer!.
Qed.

Lemma mbox_post_opt_sched_return : forall environment critical saved_local sg original returned mask
  pe eid message options before restored error X,
  mbox_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, true), returned) restored ->
  mbox_post_opt_safe environment critical sg original mask pe eid message options before X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  mbox_post_opt_post environment critical saved_local sg original mask pe eid message options before error X.
Proof.
  intros environment critical saved_local sg original returned mask pe eid message options before restored error X
    Hprefix Hsafe.
  pose proof (mbox_post_opt_prefix_safe_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprefix Hsafe) as Htail.
  cbn [q_post_tail] in Htail.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error X Htail).
  unfold task_resume_sched_refined_post; Intros final current.
  assert (Hresult : mbox_post_opt_caller_result environment critical sg original mask pe eid message options
    before error final current).
  { exists returned, restored, true; split; [exact Hprefix|exact (proj1 H)]. }
  pose proof (q_post_schedule_extra_tables _ _ _ _ _ _ _ _ (proj1 H)) as Htables.
  unfold mbox_post_opt_post, q_post_closed; Exists final current; rewrite Htables; entailer!.
  apply derivable1s_emp_sepcon_unfold;
    [apply derivable1_andp_elim1|apply derivable1_truep_intros].
Qed.

(** A loop prefix is represented by continuation composition, never by a
    complete event_broadcast at an intermediate nonempty bitmap. The pure
    relation does not own or manufacture any of the current heap. *)
Definition mbox_post_opt_broadcast_cont sg eid message acquired current : Prop :=
  forall suffix final, mbox_post_opt_broadcast sg eid message current suffix final ->
    exists priorities, mbox_post_opt_broadcast sg eid message acquired priorities final.

Lemma mbox_post_opt_broadcast_cont_start : forall sg eid message state,
  mbox_post_opt_broadcast_cont sg eid message state state.
Proof. intros sg eid message state suffix final Hsuffix; eauto. Qed.

Lemma mbox_post_opt_broadcast_cont_step : forall sg eid message acquired current node priority after,
  mbox_post_opt_broadcast_cont sg eid message acquired current ->
  q_post_lookup current eid node -> q_post_group current node <> 0 ->
  mbox_post_wake_result sg eid message current after priority ->
  mbox_post_opt_broadcast_cont sg eid message acquired after.
Proof.
  intros sg eid message acquired current node priority after Hcont Hnode Hgroup Hstep suffix final Hsuffix.
  apply (Hcont (priority :: suffix) final).
  eapply event_broadcast_next; eassumption.
Qed.

Lemma mbox_post_opt_broadcast_cont_done : forall sg eid message acquired current node,
  mbox_post_opt_broadcast_cont sg eid message acquired current ->
  q_post_lookup current eid node -> q_post_group current node = 0 ->
  exists priorities, mbox_post_opt_broadcast sg eid message acquired priorities current.
Proof.
  intros sg eid message acquired current node Hcont Hnode Hzero.
  apply (Hcont [] current); eapply event_broadcast_done; eassumption.
Qed.

Definition mbox_post_opt_loop_facts environment critical sg caller active mask saved pe before acquired
  eid observed initial message current node : Prop :=
  mbox_post_acquire_facts environment critical sg caller active mask saved pe message before acquired eid observed initial /\
  mbox_post_profile sg /\ valid_event_id sg eid /\ q_post_group acquired initial <> 0 /\
  UCOS2_state_inv sg current /\ q_post_lookup current eid node /\
  node.(eventType) = OS_EVENT_TYPE_MBOX /\
  mbox_post_opt_broadcast_cont sg eid message acquired current.

Definition mbox_post_opt_loop_context environment critical saved_local sg caller active mask saved pe before acquired
  eid observed initial message current node : Assertion :=
  coq_prop (mbox_post_opt_loop_facts environment critical sg caller active mask saved pe before acquired
    eid observed initial message current node) &&
  (q_post_group_frame sg current eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired current).

Definition mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask saved pe before acquired
  eid observed initial message current node tid old : Assertion :=
  coq_prop (mbox_post_opt_loop_facts environment critical sg caller active mask saved pe before acquired
    eid observed initial message current node /\ q_post_group current node <> 0 /\
    event_task_rdy_entry sg current.(TskState) eid node tid old) &&
  (q_post_wake_frame sg current eid tid **
    q_post_mask_frame environment critical saved_local sg active saved acquired current).

Lemma mbox_post_opt_loop_wake_split : forall environment critical saved_local sg caller active mask saved pe before acquired
  eid observed initial message current node,
  q_post_group current node <> 0 ->
  mbox_post_opt_loop_context environment critical saved_local sg caller active mask saved pe before acquired
    eid observed initial message current node **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group current node |--
  EX tid old,
    mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask saved pe before acquired
      eid observed initial message current node tid old **
    event_task_rdy_pre sg current.(TskState) eid node tid old 2 0
      (q_post_sched_group current) (q_post_sched_rows current).
Proof.
  intros environment critical saved_local sg caller active mask saved pe before acquired eid observed initial message current node Hgroup.
  unfold mbox_post_opt_loop_context; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hinitial [Hvalid [Hnode [Htype Hcont]]]]]]].
  sep_apply_l_atomic (q_post_group_cell_merge sg current eid node Hvalid Hnode).
  assert (Hlayout : event_object_layout_prop sg eid).
  { exact (proj2 Hprofile eid Heid). }
  sep_apply_l_atomic (mbox_post_wake_split sg current eid node Hvalid Hnode Htype Hgroup Hlayout).
  Intros tid old; Exists tid old; unfold mbox_post_opt_loop_wake_context; entailer!.
Qed.

Lemma mbox_post_opt_loop_wake_merge : forall environment critical saved_local sg caller active mask saved pe before acquired
  eid observed initial message current node tid old priority,
  mbox_post_opt_loop_wake_context environment critical saved_local sg caller active mask saved pe before acquired
    eid observed initial message current node tid old **
    event_task_rdy_post sg current.(TskState) eid node tid old message 2 0
      (q_post_sched_group current) (q_post_sched_rows current) priority |--
  EX after next,
    mbox_post_opt_loop_context environment critical saved_local sg caller active mask saved pe before acquired
      eid observed initial message after next **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group after next.
Proof.
  intros environment critical saved_local sg caller active mask saved pe before acquired eid observed initial message current node tid old priority.
  unfold mbox_post_opt_loop_wake_context; Intros.
  destruct H as [Hfacts [Hgroup Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hinitial [Hvalid [Hnode [Htype Hcont]]]]]]].
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (mbox_post_wake_merge sg current eid node tid old message priority Hvalid Hnode Htype Hentry).
  Intros after.
  pose proof (mbox_post_opt_broadcast_cont_step sg eid message acquired current node priority after
    Hcont Hnode Hgroup H) as Hnext_cont.
  destruct (mbox_post_opt_wake_decompose sg current eid node message priority after Hvalid Hnode Htype Hgroup H)
    as [selected [tail [previous [Hlist [Hold [Hpriority [Hafter [Hafter_valid Hafter_node]]]]]]]].
  subst after.
  sep_apply_l_atomic (mbox_post_mask_frame_wake_update environment critical saved_local sg active saved acquired current
    eid node selected previous message Hold).
  sep_apply_l_atomic (q_post_group_cell_split sg
    (event_wake_state sg current eid node selected previous PendMbox message PendOK)
    eid (event_set_wait_list node tail) Hafter_node).
  Intros.
  Exists (event_wake_state sg current eid node selected previous PendMbox message PendOK)
    (event_set_wait_list node tail).
  unfold mbox_post_opt_loop_context, mbox_post_opt_loop_facts; entailer!.
Qed.

Lemma mbox_post_opt_loop_start : forall environment critical saved_local sg caller active mask saved
  pe message before acquired eid observed initial,
  q_post_group acquired initial <> 0 ->
  mbox_post_group_context environment critical saved_local sg caller active mask saved pe message
    before acquired eid observed initial |--
  mbox_post_opt_loop_context environment critical saved_local sg caller active mask saved pe before acquired
    eid observed initial message acquired initial.
Proof.
  intros environment critical saved_local sg caller active mask saved pe message before acquired eid observed initial Hgroup.
  unfold mbox_post_group_context; Intros.
  pose proof H as [Hacquire Hprofile].
  pose proof Hacquire as [[Hvalid Hsave] [_ [_ [_ [Hid [_ [_ [Hnode [Htype Hg]]]]]]]]].
  pose proof (mbox_post_opt_broadcast_cont_start sg eid message acquired) as Hcont.
  unfold mbox_post_opt_loop_context, mbox_post_opt_loop_facts; entailer!.
Qed.

Lemma mbox_post_opt_loop_restore : forall environment critical saved_local sg caller active mask saved pe before acquired
  eid observed initial message options current node,
  Z.land options 1 <> 0 -> q_post_group current node = 0 ->
  mbox_post_opt_loop_context environment critical saved_local sg caller active mask saved pe before acquired
    eid observed initial message current node **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group current node |--
  mbox_post_opt_restore_pre environment critical saved_local sg caller active mask saved pe eid message options
    before acquired current 0 (mbox_post_opt_schedule_flag options).
Proof.
  intros environment critical saved_local sg caller active mask saved pe before acquired eid observed initial message options current node
    Hbroadcast Hzero.
  unfold mbox_post_opt_loop_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hinitial [Hvalid [Hnode [Htype Hcont]]]]]]].
  destruct (mbox_post_opt_broadcast_cont_done sg eid message acquired current node Hcont Hnode Hzero)
    as [priorities Hloop].
  pose proof Hacquire as [Hsave [Hpe [Hmessage [_ [_ [_ [_ [Hinitial_node Hrest]]]]]]]].
  pose proof (mbox_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbefore_type.
  pose proof (mbox_post_opt_broadcast_critical sg acquired eid initial message options priorities current
    Hinitial_node Hinitial Hbroadcast Hloop) as Hstep.
  assert (Heffect : mbox_post_opt_effect sg eid message options acquired 0 (mbox_post_opt_schedule_flag options) current).
  { exists (Z.eqb (Z.land options 4) 0); split; [reflexivity|exact Hstep]. }
  sep_apply_l_atomic (q_post_group_cell_merge sg current eid node Hvalid Hnode).
  unfold mbox_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Lemma mbox_post_opt_broadcast_preserves : forall sg eid message (P : UCOS2_Verify_State -> Prop),
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendMbox message PendOK)) ->
  forall state priorities after,
  mbox_post_opt_broadcast sg eid message state priorities after ->
  forall node, UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> P state -> P after.
Proof.
  intros sg eid message P Hpreserve state priorities after Hloop.
  induction Hloop as [state actual Hactual Hzero |
    state actual priority mid priorities after Hactual Hgroup Hstep Hloop IH];
    intros node Hvalid Hnode Htype HP.
  - exact HP.
  - assert (actual = node) by congruence; subst actual.
    destruct (mbox_post_opt_wake_decompose sg state eid node message priority mid Hvalid Hnode Htype Hgroup Hstep)
      as [tid [tail [old [Hlist [Hold [Hpriority [Hmid [Hmid_valid Hmid_node]]]]]]]].
    subst mid; eapply IH with (node := event_set_wait_list node tail).
    + exact Hmid_valid.
    + exact Hmid_node.
    + exact Htype.
    + eapply Hpreserve; eassumption.
Qed.


Lemma mbox_post_opt_scheduled_effect_preserves : forall sg eid message options (P : UCOS2_Verify_State -> Prop),
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendMbox message PendOK)) ->
  forall state node error after,
  UCOS2_state_inv sg state -> q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
  mbox_post_opt_critical sg eid message options state (error, true) after ->
  P state -> P after.
Proof.
  intros sg eid message options P Hpreserve state node error after Hvalid Hnode Htype Hstep HP.
  destruct Hstep as [actual [Hactual Hstep]]; assert (actual = node) by congruence; subst actual.
  destruct (Z.eqb (q_post_group state node) 0) eqn:Hgroup.
  - destruct Hstep as [m [Hm Hstep]].
    destruct (Z.eqb (mbox_message_ptr m) 0); destruct Hstep as [Heq _]; discriminate.
  - apply Z.eqb_neq in Hgroup; destruct Hstep as [_ Hstep].
    destruct (Z.eqb (Z.land options 1) 0).
    + destruct Hstep as [priority Hcall].
      destruct (mbox_post_opt_wake_decompose sg state eid node message priority after Hvalid Hnode Htype Hgroup Hcall)
        as [tid [tail [old [Hlist [Hold [Hpriority [-> Hrest]]]]]]].
      eapply Hpreserve; eassumption.
    + destruct Hstep as [priorities Hloop].
      eapply mbox_post_opt_broadcast_preserves; eassumption.
Qed.

Lemma mbox_post_opt_prefix_wake_decompose : forall environment critical sg original mask pe eid message options before
  returned restored error,
  UCOS2_state_inv sg before -> mbox_post_call_input critical sg original pe message before eid ->
  mbox_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, true), returned) restored ->
  exists active saved acquired observed node released,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    mbox_post_acquire_facts environment critical sg original active mask saved pe message before acquired eid observed node /\
    mbox_post_opt_critical sg eid message options acquired (error, true) released /\
    UCOS2_state_inv sg released /\
    task_resume_restore_program environment critical sg active released returned restored.
Proof.
  intros environment critical sg original mask pe eid message options before returned restored error Hvalid Hinput Hprefix.
  unfold mbox_post_opt_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb message 0) eqn:Hmessage; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 1) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  apply Z.eqb_neq in Hpe; apply Z.eqb_neq in Hmessage; apply Z.eqb_eq in Htype.
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst code schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  destruct (mbox_post_acquire_identity environment critical sg original active mask saved pe message before acquired eid
    Hvalid Hpe Hmessage Hinput Htype Hfacts) as [observed [node Hacquire]].
  pose proof Hacquire as [_ [_ [_ [_ [_ [_ [_ [Hnode [Hmbox Hg]]]]]]]]].
  pose proof (mbox_post_opt_critical_preserves_validity sg acquired eid node message options
    (error, true) released (proj1 Hfacts) Hnode Hmbox Hmessage Hstep) as Hreleased.
  exists active, saved, acquired, observed, node, released; auto.
Qed.

Lemma mbox_post_opt_schedule_protocol_null : forall environment critical sg caller mask eid message options before,
  mbox_post_opt_schedule_protocol environment critical sg caller mask 0 eid message options before.
Proof.
  intros environment critical sg caller mask eid message options before returned restored error Hprefix.
  unfold mbox_post_opt_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma mbox_post_opt_schedule_protocol_null_message : forall environment critical sg caller mask pe eid options before,
  mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid 0 options before.
Proof.
  intros environment critical sg caller mask pe eid options before returned restored error Hprefix.
  unfold mbox_post_opt_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); cbn in Hprefix; destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma mbox_post_opt_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid message options before,
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid <> 1 ->
  mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before Hpe Hmessage Htype
    returned restored error Hprefix.
  unfold mbox_post_opt_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hmessage),
    (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.


Lemma mbox_post_opt_schedule_protocol_no_sched : forall environment critical sg caller mask pe eid message options before,
  Z.land options 4 <> 0 ->
  mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before Hnosched returned restored error Hprefix.
  unfold mbox_post_opt_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb message 0); [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 1);
    [|destruct Hprefix as [Heq _]; discriminate].
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst schedule next.
  destruct Hstep as [node [Hnode Hbody]].
  destruct (Z.eqb (q_post_group acquired node) 0).
  - destruct Hbody as [m [Hm Hbody]].
    destruct (Z.eqb (mbox_message_ptr m) 0); destruct Hbody as [Heq _]; discriminate.
  - destruct Hbody as [Heq _].
    rewrite (proj2 (Z.eqb_neq _ _) Hnosched) in Heq; discriminate.
Qed.

Lemma mbox_post_opt_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid message options before,
  (forall active saved acquired node,
    task_resume_save_program environment critical sg caller mask before (active, saved) acquired ->
    q_post_lookup acquired eid node -> q_post_group acquired node = 0) ->
  mbox_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before Hempty returned restored error Hprefix.
  unfold mbox_post_opt_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb message 0); [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 1);
    [|destruct Hprefix as [Heq _]; discriminate].
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [[node [Hnode Hstep]] [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst schedule.
  rewrite (Hempty active saved acquired node Hsave Hnode) in Hstep.
  destruct Hstep as [m [Hm Hstep]].
  destruct (Z.eqb (mbox_message_ptr m) 0); destruct Hstep as [Heq _]; discriminate.
Qed.
Lemma mbox_post_opt_schedule_protocol_task : forall environment critical sg call mask pe eid message options before,
  UCOS2_state_inv sg before ->
  mbox_post_call_input critical sg (ResumeTaskCaller call) pe message before eid ->
  kernel_sched_ready_clients critical -> task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before -> before.(SchedState).(readyList) <> [] ->
  mbox_post_opt_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid message options before.
Proof.
  intros environment critical sg call mask pe eid message options before Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored error Hprefix.
  destruct (mbox_post_opt_prefix_wake_decompose environment critical sg (ResumeTaskCaller call) mask pe eid message options
    before returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [observed [node [released [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [_ [_ [_ [_ [Hnode [Hmbox Hg]]]]]]]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  assert (Hreleased_source : task_resume_caller_source sg (ResumeTaskCaller active) released).
  { eapply mbox_post_opt_scheduled_effect_preserves with
      (sg := sg) (eid := eid) (message := message) (options := options)
      (state := acquired) (node := node) (error := error)
      (P := task_resume_caller_source sg (ResumeTaskCaller active)); try eassumption.
    intros; eapply mbox_post_wake_preserves_task_source; eassumption. }
  destruct (q_post_task_restore_source environment critical sg active returned released restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hreleased_ready : released.(SchedState).(readyList) <> []).
  { eapply mbox_post_opt_scheduled_effect_preserves with
      (sg := sg) (eid := eid) (message := message) (options := options)
      (state := acquired) (node := node) (error := error)
      (P := fun s => s.(SchedState).(readyList) <> []); try eassumption.
    intros; apply mbox_post_wake_preserves_ready_nonempty; assumption. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma mbox_post_opt_schedule_protocol_disabled : forall environment critical sg view mask pe eid message options before,
  UCOS2_state_inv sg before ->
  mbox_post_call_input critical sg (ResumeGenericCaller view) pe message before eid ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  mbox_post_opt_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid message options before.
Proof.
  intros environment critical sg view mask pe eid message options before Hvalid Hinput Hclients Hsource
    returned restored error Hprefix.
  destruct (mbox_post_opt_prefix_wake_decompose environment critical sg (ResumeGenericCaller view) mask pe eid message options
    before returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [observed [node [released [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [_ [_ [_ [_ [Hnode [Hmbox Hg]]]]]]]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  assert (Hreleased_source : sched_disabled_entry_source view released).
  { eapply mbox_post_opt_scheduled_effect_preserves with
      (sg := sg) (eid := eid) (message := message) (options := options)
      (state := acquired) (node := node) (error := error)
      (P := sched_disabled_entry_source view); try eassumption.
    intros; apply mbox_post_wake_preserves_disabled_source; assumption. }
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    released restored Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma mbox_post_profile_group_address__resource_transitions : forall sg eid,
  mbox_post_profile sg -> valid_event_id sg eid ->
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) =
    event_addr sg eid + OSEventGrp_off.
Proof.
  intros sg eid Hprofile Hid.
  exact (proj1 (proj2 (proj2 Hprofile eid Hid))).
Qed.
Lemma mbox_post_opt_loop_context_profile__resource_transitions :
  forall environment critical saved_local sg caller active mask saved pe before acquired
    eid observed initial message current node,
  mbox_post_opt_loop_context environment critical saved_local sg caller active mask saved pe before acquired
    eid observed initial message current node |--
  coq_prop (mbox_post_profile sg /\ valid_event_id sg eid) &&
  mbox_post_opt_loop_context environment critical saved_local sg caller active mask saved pe before acquired
    eid observed initial message current node.
Proof.
  intros; unfold mbox_post_opt_loop_context; Intros.
  pose proof H as [_ [Hprofile [Hid _]]].
  entailer!.
Qed.
