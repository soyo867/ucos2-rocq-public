Require Export Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_wake_spec.
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

(** The fixed unnamed ECB/TCB64 profile. The layout is the source ABI binding;
    it is not an additional restriction on a runtime mailbox handle. *)
Definition mbox_post_profile (sg : StableGlobVars) : Prop :=
  mbox_accept_profile sg /\ event_table_layout_prop sg.

(** Message zero returns before any ECB read. In that branch no public
    event-slot ownership or handle-lifetime premise is required. *)
Definition mbox_post_call_input critical sg caller pe message before eid : Prop :=
  message = 0 \/ mbox_accept_call_input critical sg
    (task_resume_view caller).(os_execution_invocation) pe before eid.

Definition mbox_post_store_state state eid node message : UCOS2_Verify_State :=
  replace_EventS (update_event_field_raw state.(EventState) eid
    (mbox_set_message node (mbox_message_from_ptr message))) state.

(** This is exactly the protected branch, after the ordered public checks.
    The nonempty bitmap calls the generic checked Event wake with PendMbox.
    Otherwise the sole write is to the empty Ptr; full leaves all state alone. *)
Definition mbox_post_critical (sg : StableGlobVars) (eid : EventID) (message : addr)
  : program UCOS2_Verify_State (Z * bool) :=
  fun acquired result released =>
    exists node, q_post_lookup acquired eid node /\
      if Z.eqb (q_post_group acquired node) 0 then
        exists m, node.(mboxFields) = Some m /\
          if Z.eqb (mbox_message_ptr m) 0
          then result = (0, false) /\ released = mbox_post_store_state acquired eid node message
          else result = (20, false) /\ released = acquired
      else result = (0, true) /\
        exists priority, event_task_rdy sg acquired eid PendMbox message PendOK =
          Some (priority, released).

Lemma mbox_post_wake_head : forall sg s eid e head tail message,
  UCOS2_state_inv sg s -> q_post_lookup s eid e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX -> e.(waitList) = head :: tail ->
  exists old,
    s.(TskState).(inUsedTaskStates) head = Some old /\
    event_task_rdy sg s eid PendMbox message PendOK =
      Some (old.(curPrio), event_wake_state sg s eid e head old PendMbox message PendOK) /\
    UCOS2_state_inv sg (event_wake_state sg s eid e head old PendMbox message PendOK) /\
    (event_wake_state sg s eid e head old PendMbox message PendOK).(EventState).(inUsedEventStates) eid =
      Some (event_set_wait_list e tail).
Proof.
  intros sg s eid e head tail message Hvalid He Htype Hlist.
  apply (event_wake_head sg s eid e head tail PendMbox message PendOK);
    [exact Hvalid|exact He|rewrite Htype; reflexivity|exact Hlist].
Qed.

Lemma mbox_post_current_message : forall sg state eid node,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> q_post_group state node = 0 ->
  exists m, node.(mboxFields) = Some m /\ node.(waitList) = [] /\
    mbox_fields_consistency [] m.
Proof.
  intros sg state eid node Hvalid Hnode Htype Hgroup.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  pose proof Hevents as [_ [_ [_ [_ [Hpayload [_ Hentries]]]]]].
  pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState)
    node.(waitList) (proj1 (Hentries eid node Hnode))) Hgroup) as Hempty.
  specialize (Hpayload eid node Hnode); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct node.(mboxFields) as [m|] eqn:Hm;
    [exists m; rewrite Hempty in Hpayload; auto|contradiction].
Qed.

Lemma mbox_post_store_preserves_validity : forall sg state eid node message,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> node.(waitList) = [] -> message <> 0 ->
  UCOS2_state_inv sg (mbox_post_store_state state eid node message).
Proof.
  intros sg state eid node message Hvalid Hnode Htype Hempty Hmessage.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  unfold mbox_post_store_state; eapply UCOS2_event_payload_update_preserves_validity;
    try eassumption; try reflexivity.
  eapply mbox_set_message_preserves_event_in_range; try eassumption.
  rewrite Hempty; unfold mbox_fields_consistency.
  rewrite (mbox_message_from_ptr_nonzero message Hmessage); split; [exact Hmessage|].
  intros H; exfalso; apply H; reflexivity.
Qed.

Lemma mbox_post_critical_has_result : forall sg state eid node message,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> message <> 0 ->
  exists result after, mbox_post_critical sg eid message state result after.
Proof.
  intros sg state eid node message Hvalid Hnode Htype Hmessage.
  destruct (Z.eq_dec (q_post_group state node) 0) as [Hempty|Hnonempty].
  - destruct (mbox_post_current_message sg state eid node Hvalid Hnode Htype Hempty)
      as [m [Hm [Hwait Hconsistent]]].
    destruct (Z.eq_dec (mbox_message_ptr m) 0) as [Hzero|Hfull].
    + exists (0, false), (mbox_post_store_state state eid node message).
      exists node; split; [exact Hnode|]; rewrite Hempty.
      exists m; split; [exact Hm|]; rewrite Hzero; cbn; auto.
    + exists (20, false), state.
      exists node; split; [exact Hnode|]; rewrite Hempty.
      exists m; split; [exact Hm|]; rewrite (proj2 (Z.eqb_neq _ _) Hfull); auto.
  - destruct node.(waitList) as [|head tail] eqn:Hlist;
      [contradiction Hnonempty; unfold q_post_group; rewrite Hlist; reflexivity|].
    destruct (mbox_post_wake_head sg state eid node head tail message Hvalid Hnode Htype Hlist)
      as [old [Hold [Hstep Hrest]]].
    exists (0, true), (event_wake_state sg state eid node head old PendMbox message PendOK).
    exists node; split; [exact Hnode|]; rewrite (proj2 (Z.eqb_neq _ _) Hnonempty).
    split; [reflexivity|exists old.(curPrio); exact Hstep].
Qed.

Definition mbox_post_prefix_program environment critical sg caller mask pe eid message
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = ((4, false), caller) /\ restored = before
    else if Z.eqb message 0 then result = ((3, false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 1 then
      exists active saved acquired error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        mbox_post_critical sg eid message acquired (error, schedule) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = ((error, schedule), returned)
    else result = ((1, false), caller) /\ restored = before.

(** The shared tail is exactly Restore's optional Scheduler continuation;
    it contains neither Queue storage nor an OSRunning guard. *)
Definition mbox_post_program environment critical sg caller mask pe eid message
  : program UCOS2_Verify_State Z :=
  bind (mbox_post_prefix_program environment critical sg caller mask pe eid message)
    (q_post_tail environment critical sg mask).

Definition mbox_post_safe environment critical sg caller mask pe eid message before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (mbox_post_program environment critical sg caller mask pe eid message) X.

Definition mbox_post_caller_result environment critical sg original mask pe eid message before
  error returned current : Prop :=
  exists prefix_caller restored schedule,
    mbox_post_prefix_program environment critical sg original mask pe eid message before
      ((error, schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

(** The separated coq_prop preserves its TT residual. The same existential
    witnesses index the actual return relation, arbitrary X, and all resources. *)
Definition mbox_post_post environment critical saved_local sg original mask pe eid message before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (mbox_post_caller_result environment critical sg original mask pe eid message before error returned current /\
      q_post_return_safe current error X) **
    q_post_closed environment critical saved_local sg returned mask current.

Lemma mbox_post_program_null : forall environment critical sg caller mask eid message before,
  mbox_post_program environment critical sg caller mask 0 eid message before 4 before.
Proof.
  intros; exists ((4, false), caller), before; split.
  - unfold mbox_post_prefix_program; cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma mbox_post_program_wrong_type : forall environment critical sg caller mask pe eid message before,
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid <> 1 ->
  mbox_post_program environment critical sg caller mask pe eid message before 1 before.
Proof.
  intros; exists ((1, false), caller), before; split.
  - change (mbox_post_prefix_program environment critical sg caller mask pe eid message
      before ((1, false), caller) before).
    unfold mbox_post_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H),
      (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1); split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma mbox_post_prefix_protected : forall environment critical sg original active returned mask
  pe eid message before acquired released restored saved error schedule,
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid = 1 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  mbox_post_critical sg eid message acquired (error, schedule) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  mbox_post_prefix_program environment critical sg original mask pe eid message before
    ((error, schedule), returned) restored.
Proof.
  intros; unfold mbox_post_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0), H1; cbn.
  exists active, saved, acquired, error, schedule, released, returned; auto.
Qed.

Lemma mbox_post_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid message before restored error schedule X,
  mbox_post_prefix_program environment critical sg original mask pe eid message before
    ((error, schedule), returned) restored ->
  mbox_post_safe environment critical sg original mask pe eid message before X ->
  safeExec (fun state => state = restored)
    (q_post_tail environment critical sg mask ((error, schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid message before restored error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (mbox_post_prefix_program environment critical sg original mask pe eid message)
    (q_post_tail environment critical sg mask) (fun state => state = before)
    ((error, schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma mbox_post_program_nonschedule : forall environment critical sg original returned mask
  pe eid message before restored error,
  mbox_post_prefix_program environment critical sg original mask pe eid message before
    ((error, false), returned) restored ->
  mbox_post_program environment critical sg original mask pe eid message before error restored.
Proof.
  intros; exists ((error, false), returned), restored; split; [assumption|].
  cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma mbox_post_program_schedule : forall environment critical sg original returned final mask
  pe eid message before restored current error,
  mbox_post_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  task_resume_schedule_program environment critical sg returned mask restored final current ->
  mbox_post_program environment critical sg original mask pe eid message before error current.
Proof.
  intros; exists ((error, true), returned), restored; split; [assumption|].
  cbn [q_post_tail]; exists tt, current; split; [|split; reflexivity].
  exists final, current; split; [assumption|split; reflexivity].
Qed.

Lemma mbox_post_safe_return : forall environment critical sg caller mask pe eid message before current error X,
  mbox_post_program environment critical sg caller mask pe eid message before error current ->
  mbox_post_safe environment critical sg caller mask pe eid message before X ->
  q_post_return_safe current error X.
Proof.
  intros environment critical sg caller mask pe eid message before current error X Hprogram Hsafe.
  eapply (highstependret_derive
    (mbox_post_program environment critical sg caller mask pe eid message)
    (fun state => state = before) error (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma mbox_post_closed_return : forall environment critical saved_local sg original returned mask
  pe eid message before current error X,
  mbox_post_caller_result environment critical sg original mask pe eid message before error returned current ->
  mbox_post_safe environment critical sg original mask pe eid message before X ->
  q_post_closed environment critical saved_local sg returned mask current |--
  mbox_post_post environment critical saved_local sg original mask pe eid message before error X.
Proof.
  intros.
  assert (Hprogram : mbox_post_program environment critical sg original mask pe eid message before error current).
  { pose proof H as Hresult; destruct Hresult as [prefix_caller [restored [schedule [Hprefix Htail]]]].
    destruct schedule.
    - eapply mbox_post_program_schedule with (final := returned); eassumption.
    - destruct Htail as [-> ->]; eapply mbox_post_program_nonschedule; exact Hprefix. }
  pose proof (mbox_post_safe_return _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0).
  unfold mbox_post_post; Exists returned current; entailer!.
  apply derivable1_truep_intros.
Qed.

Lemma mbox_post_program_null_message : forall environment critical sg caller mask pe eid before,
  pe <> 0 -> mbox_post_program environment critical sg caller mask pe eid 0 before 3 before.
Proof.
  intros; exists ((3, false), caller), before; split.
  - unfold mbox_post_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H); cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Definition mbox_post_schedule_protocol environment critical sg caller mask pe eid message before : Prop :=
  forall returned restored error,
    mbox_post_prefix_program environment critical sg caller mask pe eid message before
      ((error, true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Definition mbox_post_wake_result (sg : StableGlobVars) (eid : EventID) (message : addr)
  (entry after : UCOS2_Verify_State) (priority : Z) : Prop :=
  event_task_rdy sg entry eid PendMbox message PendOK = Some (priority, after).

Lemma mbox_post_wake_split : forall sg entry eid current,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_MBOX ->
  encode_event_wait_grp current.(waitList) entry.(TskState) <> 0 ->
  event_object_layout_prop sg eid ->
  UCOS2_inv sg entry ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg entry.(TskState) eid current tid old) &&
    (event_task_rdy_pre sg entry.(TskState) eid current tid old 2 0
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
      (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     q_post_wake_frame sg entry eid tid).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype Hnonempty Hlayout.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg)
    by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  destruct current.(waitList) as [|tid tail] eqn:Hlist;
    [contradiction Hnonempty; reflexivity|].
  destruct (mbox_post_wake_head sg entry eid current tid tail 0
    Hvalid Hlookup Htype Hlist) as [old [Hold Hrest]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  assert (Hentry : event_task_rdy_entry sg entry.(TskState) eid current tid old).
  { unfold event_task_rdy_entry; split; [exact Hsg|]; split; [exact Hlayout|].
    split; [exact Hmulti|]; split; [exact Htasks|].
    split; [exact (Hentries eid current Hlookup)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  rewrite UCOS2_inv_open_task_storage_sched_event; Intros.
  sep_apply_l_atomic (q_post_task_storage_split sg entry.(TskState) tid old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists tid old; unfold event_task_rdy_pre, q_post_wake_frame, used_event_rep.
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma mbox_post_wake_merge : forall sg entry eid current tid old message priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_MBOX ->
  event_task_rdy_entry sg entry.(TskState) eid current tid old ->
  event_task_rdy_post sg entry.(TskState) eid current tid old message 2 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  q_post_wake_frame sg entry eid tid |-- EX after,
    coq_prop (mbox_post_wake_result sg eid message entry after priority) &&
    (UCOS2_inv sg after ** unmap_table_rep sg).
Proof.
  intros sg entry eid current tid old message priority Hvalid Hlookup Htype Hentry.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg entry.(TskState) eid current tid old Hentry)
    as [_ [_ [_ [Hprio _]]]].
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendMbox)
    by (rewrite Htype; reflexivity).
  destruct current.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (mbox_post_wake_head sg entry eid current tid tail message
    Hvalid Hlookup Htype Hlist) as [found [Hfound [Hstep [Hafter Hlast]]]].
  assert (found = old) by congruence; subst found.
  unfold event_task_rdy_post, q_post_wake_frame; Intros.
  assert (Hreturned : priority = old.(curPrio)) by tauto; subst priority.
  rewrite (event_task_rdy_typed_image_eq sg old message 2 0 PendMbox PendOK eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold Hprio).
  sep_apply_l_atomic (q_post_task_storage_merge sg entry.(TskState) tid
    (task_event_wake_single old PendMbox message PendOK) Hmulti Hprofiling).
  fold (used_event_rep sg entry.(TskState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg entry.(TskState) entry.(EventState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg entry.(TskState) entry.(SchedState) tid
    (task_status_clear_wait (encode_task_status old.(stat)) 2)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 2 =
    encode_task_status (task_event_wake_single old PendMbox message PendOK).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 2 =
      encode_task_status (task_clear_pending_status old.(stat) PendMbox)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  unfold task.encode_task_status in *; rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendMbox message PendOK)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
    (encode_task_status (task_event_wake_single old PendMbox message PendOK).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) entry.(TskState) **
    sched_rows_rep sg entry.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendMbox message PendOK)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (UCOS2_inv_merge_event_wake sg entry eid current tid old PendMbox message PendOK
    Hvalid Hlookup ltac:(rewrite Hlist; left; reflexivity) Hold Hkind) as Hmerge.
  cbn zeta in Hmerge.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS
    TskState SchedState EventState] in Hmerge.
  unfold task.encode_task_status in Hmerge.
  fold woken_sched in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists (event_wake_state sg entry eid current tid old PendMbox message PendOK).
  unfold mbox_post_wake_result; entailer!.
Qed.

Lemma mbox_post_mask_frame_wake_update : forall environment critical saved_local sg caller saved acquired state
  eid node tid old message,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  q_post_mask_frame environment critical saved_local sg caller saved acquired state |--
  q_post_mask_frame environment critical saved_local sg caller saved acquired
    (event_wake_state sg state eid node tid old PendMbox message PendOK).
Proof.
  intros environment critical saved_local sg [call|view] saved acquired state eid node tid old message Hold;
    [|reflexivity].
  assert (Hobserve : forall slot updated,
    (event_wake_state sg state eid node tid old PendMbox message PendOK).(TskState).(inUsedTaskStates) slot = Some updated ->
    exists previous, state.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = updated.(taskGeneration) /\ previous.(tcbStkPtr) = updated.(tcbStkPtr)).
  { intros slot updated Hupdated.
    cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates] in Hupdated.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hupdated as Hupdated; subst updated;
        exists old; repeat split; assumption || reflexivity.
    - exists updated; auto. }
  unfold q_post_mask_frame; Intros.
  assert (Hcoverage : task_stack_live_coverage
    (event_wake_state sg state eid node tid old PendMbox message PendOK).(TskState)
      (task_stack_call_active_key call)).
  { eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState)).
    - intros slot updated Hupdated.
      destruct (Hobserve slot updated Hupdated) as [previous [Hprevious [Hg Hsp]]].
      exists previous; split; [exact Hprevious|symmetry; exact Hg].
    - reflexivity.
    - exact H. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local state |--
    task_tcb_init_continuation_capsules environment saved_local
      (event_wake_state sg state eid node tid old PendMbox message PendOK)).
  { unfold task_tcb_init_continuation_capsules.
    apply kernel_saved_continuation_map_reindex.
    intros key payload updated Hstack Hupdated Hg.
    destruct (Hobserve (fst key) updated Hupdated) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; repeat split; auto. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.

(** Save lends the unchanged generic or Task resources. Object identity is
    obtained separately from the existing handle protocol, never from Save. *)
Definition mbox_post_acquire_facts environment critical sg original active mask saved pe message
  before acquired eid observed current : Prop :=
  q_post_save_facts environment critical sg original active mask saved before acquired /\
  pe <> 0 /\ message <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
  q_post_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_MBOX /\
  q_post_lookup acquired eid current /\ current.(eventType) = OS_EVENT_TYPE_MBOX /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma mbox_post_acquire_identity : forall environment critical sg original active mask saved
  pe message before acquired eid,
  UCOS2_state_inv sg before -> pe <> 0 -> message <> 0 ->
  mbox_post_call_input critical sg original pe message before eid ->
  event_slot_type_value before.(EventState) eid = 1 ->
  q_post_save_facts environment critical sg original active mask saved before acquired ->
  exists observed current,
    mbox_post_acquire_facts environment critical sg original active mask saved pe message
      before acquired eid observed current.
Proof.
  intros environment critical sg original active mask saved pe message before acquired eid
    Hvalid Hpe Hmessage Hinput Htype Hsave.
  destruct Hinput as [Hzero|Hinput]; [contradiction|].
  destruct Hinput as [Hzero|[_ [Haddr [Hid [Hpublic Hprotocol]]]]]; [contradiction|].
  pose proof Htype as Hencoded; unfold event_slot_type_value in Hencoded.
  destruct (before.(EventState).(inUsedEventStates) eid) as [observed|] eqn:Hlookup;
    [|discriminate].
  apply mbox_accept_encoded_type in Hencoded.
  destruct (mutex_query_handle_interval_preserves_identity critical sg
    (task_resume_view original).(os_execution_invocation) eid before acquired observed
    (Hprotocol Htype) (proj1 (proj2 Hsave)) Hvalid Hlookup)
    as [current [Hcurrent [Hg Hkind]]].
  exists observed, current; unfold mbox_post_acquire_facts.
  split; [exact Hsave|]. split; [exact Hpe|]. split; [exact Hmessage|].
  split; [exact Haddr|]. split; [exact Hid|].
  split; [exact Hlookup|]. split; [exact Hencoded|].
  split; [exact Hcurrent|]. split; congruence.
Qed.

Lemma mbox_post_acquire_original_type : forall environment critical sg original active mask saved
  pe message before acquired eid observed current,
  mbox_post_acquire_facts environment critical sg original active mask saved pe message
    before acquired eid observed current ->
  event_slot_type_value before.(EventState) eid = 1.
Proof.
  intros environment critical sg original active mask saved pe message before acquired eid observed current
    [_ [_ [_ [_ [_ [Hlookup [Htype Hrest]]]]]]].
  unfold event_slot_type_value; rewrite Hlookup, Htype; reflexivity.
Qed.

Definition mbox_post_type_context environment saved_local sg caller mask before eid : Assertion :=
  mbox_accept_type_frame sg before eid **
  q_post_outside_frame environment saved_local sg caller mask before.

Lemma mbox_post_type_split : forall environment critical saved_local sg caller mask before pe message eid,
  UCOS2_state_inv sg before -> pe <> 0 -> message <> 0 ->
  mbox_post_call_input critical sg caller pe message before eid ->
  q_post_closed environment critical saved_local sg caller mask before |--
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value before.(EventState) eid **
  mbox_post_type_context environment saved_local sg caller mask before eid.
Proof.
  intros environment critical saved_local sg caller mask before pe message eid Hvalid Hpe Hmessage Hinput.
  destruct Hinput as [Hzero|[Hzero|[_ [Haddr [Hid [Hpublic Hprotocol]]]]]];
    try contradiction.
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  sep_apply_l_atomic (mbox_accept_type_split_full sg before eid Hpublic).
  unfold mbox_post_type_context; entailer!.
Qed.

Lemma mbox_post_type_merge : forall environment critical saved_local sg caller mask before eid,
  UCOS2_state_inv sg before ->
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value before.(EventState) eid **
  mbox_post_type_context environment saved_local sg caller mask before eid |--
  q_post_closed environment critical saved_local sg caller mask before.
Proof.
  intros; unfold mbox_post_type_context.
  sep_apply_l_atomic (mbox_accept_type_merge_full sg before eid H).
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before H).
  entailer!.
Qed.

Definition mbox_post_save_pre environment critical saved_local sg caller mask before pe message eid : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\ pe <> 0 /\ message <> 0 /\
    mbox_post_call_input critical sg caller pe message before eid /\
    event_slot_type_value before.(EventState) eid = 1) &&
  q_post_closed environment critical saved_local sg caller mask before.

Definition mbox_post_save_result environment critical saved_local sg caller mask saved before pe message eid : Assertion :=
  EX active acquired observed current,
    coq_prop (mbox_post_acquire_facts environment critical sg caller active mask saved pe message
      before acquired eid observed current) &&
    q_post_masked environment critical saved_local sg active saved acquired acquired.

Lemma mbox_post_save_pre_raw : forall environment critical saved_local sg caller mask before pe message eid,
  mbox_post_save_pre environment critical saved_local sg caller mask before pe message eid |--
  q_post_closed environment critical saved_local sg caller mask before.
Proof. intros; unfold mbox_post_save_pre; apply derivable1_andp_elim2. Qed.

Lemma mbox_post_save_result_consequence : forall environment critical saved_local sg caller mask saved before pe message eid,
  UCOS2_state_inv sg before -> pe <> 0 -> message <> 0 ->
  mbox_post_call_input critical sg caller pe message before eid ->
  event_slot_type_value before.(EventState) eid = 1 ->
  q_post_save_output environment critical saved_local sg caller mask saved before |--
  mbox_post_save_result environment critical saved_local sg caller mask saved before pe message eid.
Proof.
  intros environment critical saved_local sg caller mask saved before pe message eid
    Hvalid Hpe Hmessage Hinput Htype.
  sep_apply_l_atomic (q_post_save_output_acquire environment critical saved_local sg caller mask saved before Hvalid).
  Intros active acquired.
  destruct (mbox_post_acquire_identity environment critical sg caller active mask saved pe message before acquired eid
    Hvalid Hpe Hmessage Hinput Htype H) as [observed [current Hcurrent]].
  unfold mbox_post_save_result; Exists active acquired observed current; entailer!.
Qed.

Definition mbox_post_prefix_result environment critical sg caller mask pe eid message before
  (error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    mbox_post_prefix_program environment critical sg caller mask pe eid message before
      ((error, request), returned) current.

Definition mbox_post_effect sg eid message acquired (error schedule : Z) released : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    mbox_post_critical sg eid message acquired (error, request) released.

Definition mbox_post_restore_pre environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ message <> 0 /\ event_slot_type_value before.(EventState) eid = 1 /\
    UCOS2_state_inv sg released /\ mbox_post_effect sg eid message acquired error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before error schedule : Assertion :=
  EX returned current,
    coq_prop (mbox_post_prefix_result environment critical sg caller mask pe eid message before
      error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma mbox_post_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule,
  mbox_post_restore_pre environment critical saved_local sg caller active mask saved pe eid message
    before acquired released error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold mbox_post_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma mbox_post_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid = 1 ->
  UCOS2_state_inv sg released -> mbox_post_effect sg eid message acquired error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid message before acquired released error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Hmessage Htype Hvalid [request [-> Hstep]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : mbox_post_prefix_result environment critical sg caller mask pe eid message before
    error (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply mbox_post_prefix_protected;
      [exact Hpe|exact Hmessage|exact Htype|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold mbox_post_restore_post; Exists returned current; entailer!.
Qed.

Lemma mbox_post_nonschedule_return : forall environment critical saved_local sg caller mask pe eid message before error X,
  mbox_post_safe environment critical sg caller mask pe eid message before X ->
  mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before error 0 |--
  mbox_post_post environment critical saved_local sg caller mask pe eid message before error X.
Proof.
  intros; unfold mbox_post_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; [discriminate|].
  assert (Hresult : mbox_post_caller_result environment critical sg caller mask pe eid message before error returned current).
  { exists returned, current, false; auto. }
  sep_apply_r_atomic (mbox_post_closed_return environment critical saved_local sg caller returned mask pe eid message before current error X Hresult H).
  entailer!.
Qed.

Lemma mbox_post_restored_schedule_pre : forall environment critical saved_local sg caller mask pe eid message before error,
  mbox_post_schedule_protocol environment critical sg caller mask pe eid message before ->
  mbox_post_restore_post environment critical saved_local sg caller mask pe eid message before error 1 |--
  EX returned current,
    coq_prop (mbox_post_prefix_result environment critical sg caller mask pe eid message before error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid message before error Hprotocol.
  unfold mbox_post_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]. pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current error Hprefix)).
  Exists returned current; entailer!.
Qed.

Lemma mbox_post_sched_return : forall environment critical saved_local sg original returned mask
  pe eid message before restored error X,
  mbox_post_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  mbox_post_safe environment critical sg original mask pe eid message before X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  mbox_post_post environment critical saved_local sg original mask pe eid message before error X.
Proof.
  intros environment critical saved_local sg original returned mask pe eid message before restored error X
    Hprefix Hsafe.
  pose proof (mbox_post_prefix_safe_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprefix Hsafe) as Htail.
  cbn [q_post_tail] in Htail.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error X Htail).
  unfold task_resume_sched_refined_post; Intros final current.
  assert (Hresult : mbox_post_caller_result environment critical sg original mask pe eid message
    before error final current).
  { exists returned, restored, true; split; [exact Hprefix|exact (proj1 H)]. }
  pose proof (q_post_schedule_extra_tables _ _ _ _ _ _ _ _ (proj1 H)) as Htables.
  unfold mbox_post_post, q_post_closed; Exists final current; rewrite Htables; entailer!.
  apply derivable1s_emp_sepcon_unfold;
    [apply derivable1_andp_elim1|apply derivable1_truep_intros].
Qed.

Definition mbox_post_group_context environment critical saved_local sg caller active mask saved pe message
  before acquired eid observed current : Assertion :=
  coq_prop (mbox_post_acquire_facts environment critical sg caller active mask saved pe message
    before acquired eid observed current /\ mbox_post_profile sg) &&
  (q_post_group_frame sg acquired eid current ** unmap_table_rep sg **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Definition mbox_post_wake_context environment critical saved_local sg caller active mask saved pe message
  before acquired eid observed current tid old : Assertion :=
  coq_prop (mbox_post_acquire_facts environment critical sg caller active mask saved pe message
    before acquired eid observed current /\ mbox_post_profile sg /\ q_post_group acquired current <> 0 /\
    event_task_rdy_entry sg acquired.(TskState) eid current tid old) &&
  (q_post_wake_frame sg acquired eid tid **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Definition mbox_post_message_context environment critical saved_local sg caller active mask saved pe message
  before acquired eid observed current m : Assertion :=
  coq_prop (mbox_post_acquire_facts environment critical sg caller active mask saved pe message
    before acquired eid observed current /\ mbox_post_profile sg /\ q_post_group acquired current = 0 /\
    current.(mboxFields) = Some m /\ current.(waitList) = [] /\ mbox_fields_consistency [] m) &&
  (q_post_field_frame sg acquired eid current EventPtrField ** unmap_table_rep sg **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Lemma mbox_post_message_split : forall sg state eid node m,
  q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
  node.(mboxFields) = Some m ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr m **
     q_post_field_frame sg state eid node EventPtrField).
Proof.
  intros sg state eid node m Hnode Htype Hm.
  pose proof (q_post_field_split_full sg state eid node EventPtrField Hnode ltac:(simpl; tauto)) as Hsplit.
  cbn [event_image event_cell event_field_offset] in Hsplit.
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value in Hsplit.
  rewrite Htype, Hm in Hsplit; exact Hsplit.
Qed.

Lemma mbox_post_message_merge_original : forall sg state eid node m,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> node.(mboxFields) = Some m ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> mbox_message_ptr m **
    q_post_field_frame sg state eid node EventPtrField |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node m Hvalid Hnode Htype Hm.
  pose proof (q_post_field_merge_full sg state eid node EventPtrField Hvalid Hnode ltac:(simpl; tauto)) as Hmerge.
  cbn [event_image event_cell event_field_offset] in Hmerge.
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value in Hmerge.
  rewrite Htype, Hm in Hmerge; exact Hmerge.
Qed.

Lemma mbox_post_message_merge_updated : forall sg state eid node message,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> node.(waitList) = [] -> message <> 0 ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> message **
    q_post_field_frame sg state eid node EventPtrField |--
  UCOS2_inv sg (mbox_post_store_state state eid node message).
Proof.
  intros sg state eid node message Hvalid Hnode Htype Hempty Hmessage.
  pose proof (mbox_post_store_preserves_validity sg state eid node message Hvalid Hnode Htype Hempty Hmessage)
    as Hpost.
  pose proof (mbox_rep_merge_updated_message sg state.(TskState) eid node
    (mbox_message_from_ptr message) Htype) as Hmerge.
  rewrite mbox_message_ptr_from_ptr in Hmerge.
  unfold q_post_field_frame; fold (mbox_rep_no_message sg state.(TskState) eid node).
  sep_apply_l_atomic Hmerge.
  unfold mbox_post_store_state in *.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_event sg state eid node
    (mbox_set_message node (mbox_message_from_ptr message)) Hpost Hnode eq_refl eq_refl).
  entailer!.
Qed.

Lemma mbox_post_wake_critical : forall sg entry eid current message priority after,
  q_post_lookup entry eid current -> q_post_group entry current <> 0 ->
  mbox_post_wake_result sg eid message entry after priority ->
  mbox_post_critical sg eid message entry (0, true) after.
Proof.
  intros; exists current; split; [exact H|].
  rewrite (proj2 (Z.eqb_neq _ _) H0); split; [reflexivity|exists priority; exact H1].
Qed.

Lemma mbox_post_full_critical : forall sg entry eid current m message,
  q_post_lookup entry eid current -> current.(mboxFields) = Some m ->
  q_post_group entry current = 0 -> mbox_message_ptr m <> 0 ->
  mbox_post_critical sg eid message entry (20, false) entry.
Proof.
  intros; exists current; split; [exact H|]; rewrite H1.
  exists m; split; [exact H0|]; rewrite (proj2 (Z.eqb_neq _ _) H2); auto.
Qed.

Lemma mbox_post_store_critical : forall sg entry eid current m message,
  q_post_lookup entry eid current -> current.(mboxFields) = Some m ->
  q_post_group entry current = 0 -> mbox_message_ptr m = 0 ->
  mbox_post_critical sg eid message entry (0, false)
    (mbox_post_store_state entry eid current message).
Proof.
  intros; exists current; split; [exact H|]; rewrite H1.
  exists m; split; [exact H0|]; rewrite H2; cbn; auto.
Qed.

Lemma mbox_post_store_matches_message_operation : forall m message,
  mbox_fields_consistency [] m -> mbox_message_ptr m = 0 -> message <> 0 ->
  mbox_store m message = (OS_ERR_NONE, mbox_message_from_ptr message).
Proof.
  intros [old] message Hconsistent Hzero Hmessage.
  destruct old as [old|]; cbn [mbox_message_ptr] in Hzero.
  - destruct Hconsistent as [Hnonzero _]; contradiction.
  - rewrite mbox_store_empty by (try reflexivity; exact Hmessage).
    unfold mbox_message_from_ptr; rewrite (proj2 (Z.eqb_neq _ _) Hmessage); reflexivity.
Qed.

Lemma mbox_post_schedule_protocol_null : forall environment critical sg caller mask eid message before,
  mbox_post_schedule_protocol environment critical sg caller mask 0 eid message before.
Proof.
  intros environment critical sg caller mask eid message before returned restored error Hprefix.
  unfold mbox_post_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma mbox_post_schedule_protocol_null_message : forall environment critical sg caller mask pe eid before,
  mbox_post_schedule_protocol environment critical sg caller mask pe eid 0 before.
Proof.
  intros environment critical sg caller mask pe eid before returned restored error Hprefix.
  unfold mbox_post_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); cbn in Hprefix; destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma mbox_post_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid message before,
  pe <> 0 -> message <> 0 -> event_slot_type_value before.(EventState) eid <> 1 ->
  mbox_post_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros environment critical sg caller mask pe eid message before Hpe Hmessage Htype
    returned restored error Hprefix.
  unfold mbox_post_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hmessage),
    (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma mbox_post_prefix_wake_decompose : forall environment critical sg original mask pe eid message before
  returned restored error,
  UCOS2_state_inv sg before ->
  mbox_post_call_input critical sg original pe message before eid ->
  mbox_post_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  exists active saved acquired node tid old,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    acquired.(TskState).(inUsedTaskStates) tid = Some old /\
    UCOS2_state_inv sg (event_wake_state sg acquired eid node tid old PendMbox message PendOK) /\
    task_resume_restore_program environment critical sg active
      (event_wake_state sg acquired eid node tid old PendMbox message PendOK) returned restored.
Proof.
  intros environment critical sg original mask pe eid message before returned restored error Hvalid Hinput Hprefix.
  unfold mbox_post_prefix_program in Hprefix.
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
  destruct Hstep as [actual [Hactual Hstep]].
  assert (actual = node) by congruence; subst actual.
  destruct (Z.eqb (q_post_group acquired node) 0) eqn:Hgroup.
  - destruct Hstep as [m [Hm Hstep]].
    destruct (Z.eqb (mbox_message_ptr m) 0); destruct Hstep as [Heq _]; discriminate.
  - destruct Hstep as [Hcode [priority Hcall]].
    destruct (event_wake_decompose sg acquired eid node PendMbox message PendOK priority released
      (proj1 Hfacts) Hnode ltac:(rewrite Hmbox; reflexivity)
      (proj1 (Z.eqb_neq _ _) Hgroup) Hcall)
      as [tid [tail [old [Hlist [Hold [Hpriority [-> [Hreleased Hlast]]]]]]]].
    exists active, saved, acquired, node, tid, old; auto.
Qed.

(** No-wait calls have no scheduling admission, even in generic boot
    contexts. The premise concerns the actual acquired mailbox, not entry
    bytes which may change during the Save interval. *)
Lemma mbox_post_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid message before,
  (forall active saved acquired node,
    task_resume_save_program environment critical sg caller mask before (active, saved) acquired ->
    q_post_lookup acquired eid node -> q_post_group acquired node = 0) ->
  mbox_post_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros environment critical sg caller mask pe eid message before Hempty returned restored error Hprefix.
  unfold mbox_post_prefix_program in Hprefix.
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
Lemma mbox_post_wake_preserves_ready_members : forall sg state eid node tid old message slot,
  In slot state.(SchedState).(readyList) ->
  In slot (event_wake_state sg state eid node tid old PendMbox message PendOK).(SchedState).(readyList).
Proof.
  intros; apply (proj2 (sched_wake_by_status_membership _ _ _ _ _ _)); left; exact H.
Qed.

Lemma mbox_post_wake_preserves_ready_nonempty : forall sg state eid node tid old message,
  state.(SchedState).(readyList) <> [] ->
  (event_wake_state sg state eid node tid old PendMbox message PendOK).(SchedState).(readyList) <> [].
Proof.
  intros sg state eid node tid old message Hready.
  destruct state.(SchedState).(readyList) as [|slot tail] eqn:Hlist; [contradiction|].
  pose proof (mbox_post_wake_preserves_ready_members sg state eid node tid old message slot
    ltac:(rewrite Hlist; left; reflexivity)) as Hmember.
  intro Hempty; rewrite Hempty in Hmember; contradiction.
Qed.

Lemma mbox_post_wake_preserves_disabled_source : forall sg state eid node tid old message view,
  sched_disabled_entry_source view state ->
  sched_disabled_entry_source view (event_wake_state sg state eid node tid old PendMbox message PendOK).
Proof.
  intros sg state eid node tid old message view Hsource.
  unfold sched_disabled_entry_source, sched_disabled_isr_source in *.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS IntrState SchedState].
  rewrite sched_wake_by_status_running_eq; exact Hsource.
Qed.

Lemma mbox_post_wake_preserves_task_source : forall sg state eid node tid old message call,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_resume_caller_source sg (ResumeTaskCaller call) state ->
  task_resume_caller_source sg (ResumeTaskCaller call)
    (event_wake_state sg state eid node tid old PendMbox message PendOK).
Proof.
  intros sg state eid node tid old message call Hold [[Horigin [Hactive Hcurrent]] [Havailable Haddress]].
  assert (Hcur : (event_wake_state sg state eid node tid old PendMbox message PendOK).(SchedState).(curTaskID) =
    state.(SchedState).(curTaskID)).
  { cbn [event_wake_state replace_SchedS SchedState].
    unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity. }
  unfold task_resume_caller_source, kernel_call_task_source.
  split; [|split; [exact Havailable|exact Haddress]].
  split; [exact Horigin|]; split.
  - eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hold|reflexivity|exact Hactive].
  - unfold task_execution_current in *.
    destruct call.(os_sched_call_origin); [exact I|rewrite Hcur; exact Hcurrent].
Qed.

Lemma mbox_post_schedule_protocol_task : forall environment critical sg call mask pe eid message before,
  UCOS2_state_inv sg before ->
  mbox_post_call_input critical sg (ResumeTaskCaller call) pe message before eid ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  before.(SchedState).(readyList) <> [] ->
  mbox_post_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid message before.
Proof.
  intros environment critical sg call mask pe eid message before Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored error Hprefix.
  destruct (mbox_post_prefix_wake_decompose environment critical sg (ResumeTaskCaller call) mask pe eid message
    before returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [tid [old [Hsave [Hold [Hreleased Hrestore]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  pose proof (mbox_post_wake_preserves_task_source sg acquired eid node tid old message active Hold Hactive)
    as Hreleased_source.
  destruct (q_post_task_restore_source environment critical sg active returned
    (event_wake_state sg acquired eid node tid old PendMbox message PendOK) restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; [exact Hclients|exact Hreturn_interval|exact Hreleased|].
    apply mbox_post_wake_preserves_ready_nonempty; exact Hacquired_ready. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma mbox_post_schedule_protocol_disabled : forall environment critical sg view mask pe eid message before,
  UCOS2_state_inv sg before ->
  mbox_post_call_input critical sg (ResumeGenericCaller view) pe message before eid ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  mbox_post_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid message before.
Proof.
  intros environment critical sg view mask pe eid message before Hvalid Hinput Hclients Hsource
    returned restored error Hprefix.
  destruct (mbox_post_prefix_wake_decompose environment critical sg (ResumeGenericCaller view) mask pe eid message
    before returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [tid [old [Hsave [Hold [Hreleased Hrestore]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  pose proof (mbox_post_wake_preserves_disabled_source sg acquired eid node tid old message view Hacquired_source)
    as Hreleased_source.
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    (event_wake_state sg acquired eid node tid old PendMbox message PendOK) restored
    Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.
