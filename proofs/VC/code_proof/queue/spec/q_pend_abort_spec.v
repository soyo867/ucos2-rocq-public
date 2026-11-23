Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.

Import UCOS2_C_Rules.

(** OSQPendAbort, V2.93.01 os_q.c:564--620.  The safety/argument
    observations and all counted-loop proofs are shared with the two
    source-identical Event-family APIs.  These are source parameter
    bindings, not a second representation or another proof of the loop.
    Queue payload/QCB/buffer resources are not modified by abort. *)
Definition q_pend_abort_type_error (type_byte : Z) : option OSErrCode :=
  event_pend_abort_type_error (encode_event_type OS_EVENT_TYPE_Q) type_byte.

Definition q_pend_abort_critical (sg : StableGlobVars) (eid : EventID) (opt : Z)
  : program UCOS2_Verify_State (Z * (OSErrCode * bool)) :=
  event_pend_abort_critical sg eid PendQ opt.

Require Export Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
Require Export Ucos2Verify.VC.code.queue.q_post_source_protocol.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Coq.Lists.List Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Keep the pointer equation abstract to the C frontend so an
    uninitialized output cell is not eagerly renamed at loop joins. *)
Definition q_pend_abort_output_address (expected actual : Z) : Prop := actual = expected.

(** The protected count is carried across Restore and the actual Scheduler
    call.  The output byte is stored by C only after that call returns. *)
Definition q_pend_abort_prefix_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State (((Z * Z) * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = (((0, 4), false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 2 then
      exists active saved acquired count error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        q_pend_abort_critical sg eid (unsigned_last_nbits opt 8) acquired
          (count, (error, schedule)) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = (((count, encode_os_err_code error), schedule), returned)
    else result = (((0, 1), false), caller) /\ restored = before.

Definition q_pend_abort_tail environment critical sg mask
  (result : ((Z * Z) * bool) * TaskResumeCaller)
  : program UCOS2_Verify_State (Z * Z) :=
  if snd (fst result) then
    bind (task_resume_schedule_call_program environment critical sg (snd result) mask)
      (fun _ => StateRelMonad.ret (fst (fst result)))
  else StateRelMonad.ret (fst (fst result)).

Definition q_pend_abort_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State (Z * Z) :=
  bind (q_pend_abort_prefix_program environment critical sg caller mask pe eid opt)
    (q_pend_abort_tail environment critical sg mask).

Definition q_pend_abort_safe environment critical sg caller mask pe eid opt before
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (q_pend_abort_program environment critical sg caller mask pe eid opt) X.

Definition q_pend_abort_return_safe current count error
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret (count, error)) X.

Definition q_pend_abort_caller_result environment critical sg original mask pe eid opt before
  count error returned current : Prop :=
  exists prefix_caller restored schedule,
    q_pend_abort_prefix_program environment critical sg original mask pe eid opt before
      (((count, error), schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition q_pend_abort_post environment critical saved_local sg original mask pe eid opt before
  error_addr count (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX error returned current,
    coq_prop (q_pend_abort_caller_result environment critical sg original mask pe eid opt before
      count error returned current /\ q_pend_abort_return_safe current count error X) &&
    (q_post_closed environment critical saved_local sg returned mask current **
      error_addr # UChar |-> error).

Definition q_pend_abort_schedule_protocol environment critical sg caller mask pe eid opt before : Prop :=
  forall returned restored count error,
    q_pend_abort_prefix_program environment critical sg caller mask pe eid opt before
      (((count, error), true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Lemma q_pend_abort_prefix_protected : forall environment critical sg original active returned mask
  pe eid opt before acquired released restored saved count error schedule,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  q_pend_abort_critical sg eid (unsigned_last_nbits opt 8) acquired (count, (error, schedule)) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  q_pend_abort_prefix_program environment critical sg original mask pe eid opt before
    (((count, encode_os_err_code error), schedule), returned) restored.
Proof.
  intros; unfold q_pend_abort_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0; cbn.
  exists active, saved, acquired, count, error, schedule, released, returned; auto.
Qed.

Lemma q_pend_abort_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid opt before restored count error schedule X,
  q_pend_abort_prefix_program environment critical sg original mask pe eid opt before
    (((count, error), schedule), returned) restored ->
  q_pend_abort_safe environment critical sg original mask pe eid opt before X ->
  safeExec (fun state => state = restored)
    (q_pend_abort_tail environment critical sg mask (((count, error), schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid opt before restored count error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (q_pend_abort_prefix_program environment critical sg original mask pe eid opt)
    (q_pend_abort_tail environment critical sg mask) (fun state => state = before)
    (((count, error), schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_pend_abort_result_program : forall environment critical sg original mask pe eid opt before
  count error returned current,
  q_pend_abort_caller_result environment critical sg original mask pe eid opt before
    count error returned current ->
  q_pend_abort_program environment critical sg original mask pe eid opt before (count, error) current.
Proof.
  intros environment critical sg original mask pe eid opt before count error returned current
    [prefix_caller [restored [schedule [Hprefix Htail]]]].
  exists (((count, error), schedule), prefix_caller), restored; split; [exact Hprefix|].
  destruct schedule; cbn [q_pend_abort_tail].
  - exists tt, current; split; [|split; reflexivity].
    exists returned, current; split; [exact Htail|split; reflexivity].
  - destruct Htail as [-> ->]; split; reflexivity.
Qed.

Lemma q_pend_abort_safe_return : forall environment critical sg caller mask pe eid opt before current count error X,
  q_pend_abort_program environment critical sg caller mask pe eid opt before (count, error) current ->
  q_pend_abort_safe environment critical sg caller mask pe eid opt before X ->
  q_pend_abort_return_safe current count error X.
Proof.
  intros environment critical sg caller mask pe eid opt before current count error X Hprogram Hsafe.
  eapply (highstependret_derive
    (q_pend_abort_program environment critical sg caller mask pe eid opt)
    (fun state => state = before) (count, error) (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_pend_abort_closed_return : forall environment critical saved_local sg original returned mask
  pe eid opt before current error_addr count error X,
  q_pend_abort_caller_result environment critical sg original mask pe eid opt before
    count error returned current ->
  q_pend_abort_safe environment critical sg original mask pe eid opt before X ->
  q_post_closed environment critical saved_local sg returned mask current **
    error_addr # UChar |-> error |--
  q_pend_abort_post environment critical saved_local sg original mask pe eid opt before error_addr count X.
Proof.
  intros.
  pose proof (q_pend_abort_result_program _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hprogram.
  pose proof (q_pend_abort_safe_return _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0) as Hsafe.
  unfold q_pend_abort_post; Exists error returned current; entailer!.
Qed.

(** A prefix relates the actual current heap to the initial acquired heap.
    It does not assume that the C loop or any future call returns. *)
Definition q_pend_abort_progress sg eid acquired current (processed : list Priority) : Prop :=
  forall suffix final,
    event_broadcast sg eid PendQ 0 PendAbort current suffix final ->
    event_broadcast sg eid PendQ 0 PendAbort acquired (processed ++ suffix) final.

Lemma q_pend_abort_progress_initial : forall sg eid state,
  q_pend_abort_progress sg eid state state [].
Proof. intros sg eid state suffix final Hsuffix; exact Hsuffix. Qed.

Lemma q_pend_abort_progress_step : forall sg eid acquired current processed node priority next,
  q_pend_abort_progress sg eid acquired current processed ->
  q_post_lookup current eid node -> q_post_group current node <> 0 ->
  event_task_rdy sg current eid PendQ 0 PendAbort = Some (priority, next) ->
  q_pend_abort_progress sg eid acquired next (processed ++ [priority]).
Proof.
  intros sg eid acquired current processed node priority next Hprefix Hnode Hgroup Hstep suffix final Hsuffix.
  rewrite <- app_assoc; cbn.
  apply Hprefix; eapply event_broadcast_next; eassumption.
Qed.

Lemma q_pend_abort_progress_done : forall sg eid acquired current processed node,
  q_pend_abort_progress sg eid acquired current processed ->
  q_post_lookup current eid node -> q_post_group current node = 0 ->
  event_broadcast sg eid PendQ 0 PendAbort acquired processed current.
Proof.
  intros.
  rewrite <- (app_nil_r processed).
  apply H; eapply event_broadcast_done; eassumption.
Qed.

Lemma q_pend_abort_progress_count_bound : forall sg eid acquired current processed initial node,
  UCOS2_state_inv sg acquired -> q_post_lookup acquired eid initial ->
  initial.(eventType) = OS_EVENT_TYPE_Q ->
  UCOS2_state_inv sg current -> q_post_lookup current eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q ->
  q_pend_abort_progress sg eid acquired current processed ->
  Z.of_nat (length processed) <= 255 /\
  event_pend_abort_count processed = Z.of_nat (length processed).
Proof.
  intros sg eid acquired current processed initial node Hacquired Hinitial Hinitial_type
    Hcurrent Hnode Htype Hprogress.
  destruct (event_broadcast_exists node.(waitList) sg current eid node PendQ 0 PendAbort
    Hcurrent Hnode ltac:(rewrite Htype; reflexivity) eq_refl)
    as [suffix [final [Hsuffix Hrest]]].
  pose proof (Hprogress suffix final Hsuffix) as Hwhole.
  pose proof (event_broadcast_result sg acquired eid initial PendQ 0 PendAbort (processed ++ suffix) final
    Hacquired Hinitial ltac:(rewrite Hinitial_type; reflexivity) Hwhole) as [_ [_ [Hlength _]]].
  pose proof (event_waiter_count_le_task_count sg acquired eid initial Hacquired Hinitial) as Hwaiters.
  pose proof (task_count_in_pool_range sg acquired.(TskState)
    (proj1 Hacquired) (proj1 (proj2 Hacquired))) as Hcount.
  rewrite length_app in Hlength.
  assert (Hbound : Z.of_nat (length processed) <= 255) by lia.
  split; [exact Hbound|apply event_pend_abort_count_eq_length; exact Hbound].
Qed.

Lemma q_pend_abort_empty_critical : forall sg eid opt state node,
  q_post_lookup state eid node -> q_post_group state node = 0 ->
  q_pend_abort_critical sg eid opt state (0, (OS_ERR_NONE, false)) state.
Proof.
  intros; unfold q_post_group in H0.
  exists node; split; [exact H|]; rewrite H0; split; reflexivity.
Qed.

Lemma q_pend_abort_single_critical : forall sg eid opt state node priority after,
  q_post_lookup state eid node -> q_post_group state node <> 0 -> opt <> 1 ->
  event_task_rdy sg state eid PendQ 0 PendAbort = Some (priority, after) ->
  q_pend_abort_critical sg eid opt state (1, (OS_ERR_PEND_ABORT, true)) after.
Proof.
  intros; unfold q_post_group in H0; exists node; split; [exact H|].
  rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1).
  exists priority; split; [exact H2|reflexivity].
Qed.

Lemma q_pend_abort_broadcast_critical : forall sg eid state node priorities after,
  q_post_lookup state eid node -> q_post_group state node <> 0 ->
  event_broadcast sg eid PendQ 0 PendAbort state priorities after ->
  q_pend_abort_critical sg eid 1 state
    (event_pend_abort_count priorities, (OS_ERR_PEND_ABORT, true)) after.
Proof.
  intros; unfold q_post_group in H0; exists node; split; [exact H|].
  rewrite (proj2 (Z.eqb_neq _ _) H0); cbn.
  exists priorities; split; [exact H1|reflexivity].
Qed.

Lemma q_pend_abort_wake_split : forall sg state eid node,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> q_post_group state node <> 0 ->
  event_object_layout_prop sg eid ->
  UCOS2_inv sg state ** unmap_table_rep sg |-- EX tid old,
    coq_prop (event_task_rdy_entry sg state.(TskState) eid node tid old) &&
    (event_task_rdy_pre sg state.(TskState) eid node tid old 4 2
      (q_post_sched_group state) (q_post_sched_rows state) ** q_post_wake_frame sg state eid tid).
Proof.
  intros.
  sep_apply_l_atomic (q_post_wake_split sg state eid node H H0 H1 H2 H3).
  Intros tid old; Exists tid old; unfold event_task_rdy_pre; entailer!.
Qed.

Lemma q_pend_abort_wake_merge : forall sg state eid node tid old priority,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q ->
  event_task_rdy_entry sg state.(TskState) eid node tid old ->
  event_task_rdy_post sg state.(TskState) eid node tid old 0 4 2
    (q_post_sched_group state) (q_post_sched_rows state) priority **
  q_post_wake_frame sg state eid tid |--
  coq_prop (event_task_rdy sg state eid PendQ 0 PendAbort =
    Some (priority, event_wake_state sg state eid node tid old PendQ 0 PendAbort)) &&
  (UCOS2_inv sg (event_wake_state sg state eid node tid old PendQ 0 PendAbort) ** unmap_table_rep sg).
Proof.
  intros sg state eid node tid old priority Hvalid Hlookup Htype Hentry.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg state.(TskState) eid node tid old Hentry)
    as [_ [_ [_ [Hprio _]]]].
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendQ)
    by (rewrite Htype; reflexivity).
  destruct node.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg state eid node tid tail PendQ 0 PendAbort
    Hvalid Hlookup Hkind Hlist) as [found [Hfound [Hstep [Hafter Hlast]]]].
  assert (found = old) by congruence; subst found.
  unfold event_task_rdy_post, q_post_wake_frame, q_post_sched_group, q_post_sched_rows; Intros.
  assert (Hreturned : priority = old.(curPrio)) by tauto; subst priority.
  rewrite (event_task_rdy_typed_image_eq sg old 0 4 2 PendQ PendAbort eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg state.(TskState) state.(SchedState) tid old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg state.(TskState) state.(SchedState) tid old _ Hold Hprio).
  sep_apply_l_atomic (q_post_task_storage_merge sg state.(TskState) tid
    (task_event_wake_single old PendQ 0 PendAbort) Hmulti Hprofiling).
  fold (used_event_rep sg state.(TskState) eid
    (event_set_wait_list node (remove_Z_eqb tid node.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg state.(TskState) state.(EventState) eid
    (event_set_wait_list node (remove_Z_eqb tid node.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg state.(TskState) state.(SchedState) tid
    (task_status_clear_wait (encode_task_status old.(stat)) 4)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 4 =
    encode_task_status (task_event_wake_single old PendQ 0 PendAbort).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 4 =
      encode_task_status (task_clear_pending_status old.(stat) PendQ)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg state.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid
      (task_event_wake_single old PendQ 0 PendAbort)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg state.(TskState) state.(SchedState) tid
    (encode_task_status (task_event_wake_single old PendQ 0 PendAbort).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) state.(TskState) **
    sched_rows_rep sg state.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid
      (task_event_wake_single old PendQ 0 PendAbort)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (UCOS2_inv_merge_event_wake sg state eid node tid old PendQ 0 PendAbort
    Hvalid Hlookup ltac:(rewrite Hlist; left; reflexivity) Hold Hkind) as Hmerge.
  cbn zeta in Hmerge.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS
    TskState SchedState EventState] in Hmerge.
  fold woken_sched in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma q_pend_abort_mask_frame_wake_update : forall environment critical saved_local sg caller saved acquired state
  eid node tid old,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  q_post_mask_frame environment critical saved_local sg caller saved acquired state |--
  q_post_mask_frame environment critical saved_local sg caller saved acquired
    (event_wake_state sg state eid node tid old PendQ 0 PendAbort).
Proof.
  intros environment critical saved_local sg [call|view] saved acquired state eid node tid old Hold;
    [|reflexivity].
  assert (Hobserve : forall slot updated,
    (event_wake_state sg state eid node tid old PendQ 0 PendAbort).(TskState).(inUsedTaskStates) slot = Some updated ->
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
    (event_wake_state sg state eid node tid old PendQ 0 PendAbort).(TskState)
      (task_stack_call_active_key call)).
  { eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState)).
    - intros slot updated Hupdated.
      destruct (Hobserve slot updated Hupdated) as [previous [Hprevious [Hg Hsp]]].
      exists previous; split; [exact Hprevious|symmetry; exact Hg].
    - reflexivity.
    - exact H. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local state |--
    task_tcb_init_continuation_capsules environment saved_local
      (event_wake_state sg state eid node tid old PendQ 0 PendAbort)).
  { unfold task_tcb_init_continuation_capsules.
    apply kernel_saved_continuation_map_reindex.
    intros key payload updated Hstack Hupdated Hg.
    destruct (Hobserve (fst key) updated Hupdated) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; repeat split; auto. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.

Definition q_pend_abort_effect sg eid opt acquired (count error schedule : Z) released : Prop :=
  exists code (request : bool),
    error = encode_os_err_code code /\ schedule = (if request then 1 else 0) /\
    q_pend_abort_critical sg eid (unsigned_last_nbits opt 8) acquired (count, (code, request)) released.

Definition q_pend_abort_prefix_result environment critical sg caller mask pe eid opt before
  (count error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    q_pend_abort_prefix_program environment critical sg caller mask pe eid opt before
      (((count, error), request), returned) current.

Definition q_pend_abort_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released count error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 2 /\
    UCOS2_state_inv sg released /\ q_pend_abort_effect sg eid opt acquired count error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition q_pend_abort_restore_post environment critical saved_local sg caller mask pe eid opt before
  count error schedule : Assertion :=
  EX returned current,
    coq_prop (q_pend_abort_prefix_result environment critical sg caller mask pe eid opt before
      count error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma q_pend_abort_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released count error schedule,
  q_pend_abort_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
    before acquired released count error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold q_pend_abort_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma q_pend_abort_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released count error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  UCOS2_state_inv sg released -> q_pend_abort_effect sg eid opt acquired count error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  q_pend_abort_restore_post environment critical saved_local sg caller mask pe eid opt before count error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid opt before acquired released count error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hvalid [code [request [-> [-> Hstep]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : q_pend_abort_prefix_result environment critical sg caller mask pe eid opt before
    count (encode_os_err_code code) (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply q_pend_abort_prefix_protected;
      [exact Hpe|exact Htype|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold q_pend_abort_restore_post; Exists returned current; entailer!.
Qed.

Lemma q_pend_abort_restore_schedule : forall environment critical saved_local sg caller mask pe eid opt before count error,
  q_pend_abort_schedule_protocol environment critical sg caller mask pe eid opt before ->
  q_pend_abort_restore_post environment critical saved_local sg caller mask pe eid opt before count error 1 |--
  EX returned current,
    coq_prop (q_pend_abort_prefix_result environment critical sg caller mask pe eid opt before
      count error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid opt before count error Hprotocol.
  unfold q_pend_abort_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]; pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current count error Hprefix)).
  Exists returned current; entailer!.
Qed.

Lemma q_pend_abort_nonschedule_return : forall environment critical saved_local sg caller mask pe eid opt before
  count error error_addr X,
  q_pend_abort_safe environment critical sg caller mask pe eid opt before X ->
  q_pend_abort_restore_post environment critical saved_local sg caller mask pe eid opt before count error 0 **
    error_addr # UChar |-> error |--
  q_pend_abort_post environment critical saved_local sg caller mask pe eid opt before error_addr count X.
Proof.
  intros; unfold q_pend_abort_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid]; destruct request; [discriminate|].
  apply q_pend_abort_closed_return; [|exact H].
  exists returned, current, false; split; [exact Hprefix|split; reflexivity].
Qed.

Lemma q_pend_abort_sched_return : forall environment critical saved_local sg original returned mask
  pe eid opt before restored count error error_addr X,
  q_pend_abort_prefix_program environment critical sg original mask pe eid opt before
    (((count, error), true), returned) restored ->
  q_pend_abort_safe environment critical sg original mask pe eid opt before X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned ** error_addr # UChar |-> error |--
  q_pend_abort_post environment critical saved_local sg original mask pe eid opt before error_addr count X.
Proof.
  intros environment critical saved_local sg original returned mask pe eid opt before restored count error error_addr X
    Hprefix Hsafe.
  pose proof (q_pend_abort_prefix_safe_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprefix Hsafe) as Htail.
  cbn [q_pend_abort_tail] in Htail.
  assert (Hmapped : safeExec (fun state => state = restored)
    (bind (task_resume_schedule_call_program environment critical sg returned mask)
      (fun _ => StateRelMonad.ret error)) (fun _ state => X (count, error) state)).
  { destruct Htail as [state [-> Hwp]]; exists restored; split; [reflexivity|].
    intros value final [unit_value [middle [Hcall [Hvalue Hstate]]]].
    apply (Hwp (count, error) final).
    exists unit_value, middle; split; [exact Hcall|split; [reflexivity|exact Hstate]]. }
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error (fun _ state => X (count, error) state) Hmapped).
  unfold task_resume_sched_refined_post; Intros final current.
  pose proof (q_post_schedule_extra_tables _ _ _ _ _ _ _ _ (proj1 H)) as Htables.
  assert (Hresult : q_pend_abort_caller_result environment critical sg original mask pe eid opt before
    count error final current).
  { exists returned, restored, true; split; [exact Hprefix|exact (proj1 H)]. }
  sep_apply_r_atomic (q_pend_abort_closed_return environment critical saved_local sg original final mask
    pe eid opt before current error_addr count error X Hresult Hsafe).
  unfold q_post_closed; rewrite Htables; entailer!.
  apply derivable1_andp_elim1.
Qed.

Definition q_pend_abort_loop_facts environment critical sg caller active mask saved before acquired
  eid observed initial state node processed count : Prop :=
  q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed initial /\
  q_post_profile sg /\ valid_event_id sg eid /\ q_post_group acquired initial <> 0 /\
  UCOS2_state_inv sg state /\ q_post_lookup state eid node /\ node.(eventType) = OS_EVENT_TYPE_Q /\
  q_pend_abort_progress sg eid acquired state processed /\ count = event_pend_abort_count processed.

Definition q_pend_abort_loop_group_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed count : Assertion :=
  coq_prop (q_pend_abort_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed count) &&
  (q_post_group_frame sg state eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Definition q_pend_abort_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed count tid old : Assertion :=
  coq_prop (q_pend_abort_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed count /\ q_post_group state node <> 0 /\
    event_task_rdy_entry sg state.(TskState) eid node tid old) &&
  (q_post_wake_frame sg state eid tid **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Lemma q_pend_abort_progress_nonempty_count_bound : forall sg eid acquired current processed initial node,
  UCOS2_state_inv sg acquired -> q_post_lookup acquired eid initial ->
  initial.(eventType) = OS_EVENT_TYPE_Q ->
  UCOS2_state_inv sg current -> q_post_lookup current eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> q_post_group current node <> 0 ->
  q_pend_abort_progress sg eid acquired current processed ->
  0 <= event_pend_abort_count processed < 255.
Proof.
  intros sg eid acquired current processed initial node Hacquired Hinitial Hinitial_type
    Hcurrent Hnode Htype Hnonzero Hprogress.
  destruct (event_broadcast_exists node.(waitList) sg current eid node PendQ 0 PendAbort
    Hcurrent Hnode ltac:(rewrite Htype; reflexivity) eq_refl)
    as [suffix [final [Hsuffix [_ [_ [Hsuffix_length _]]]]]].
  pose proof (Hprogress suffix final Hsuffix) as Hwhole.
  pose proof (event_broadcast_result sg acquired eid initial PendQ 0 PendAbort (processed ++ suffix) final
    Hacquired Hinitial ltac:(rewrite Hinitial_type; reflexivity) Hwhole) as [_ [_ [Hlength _]]].
  pose proof (event_waiter_count_le_task_count sg acquired eid initial Hacquired Hinitial) as Hwaiters.
  pose proof (task_count_in_pool_range sg acquired.(TskState)
    (proj1 Hacquired) (proj1 (proj2 Hacquired))) as Hcount.
  assert (Hnonempty : node.(waitList) <> []) by
    (intro Hnil; unfold q_post_group in Hnonzero; rewrite Hnil in Hnonzero; contradiction Hnonzero; reflexivity).
  assert (Hpositive : (0 < length suffix)%nat).
  { rewrite Hsuffix_length; destruct node.(waitList); [contradiction|simpl; lia]. }
  rewrite length_app in Hlength.
  rewrite event_pend_abort_count_eq_length by lia; lia.
Qed.

Lemma q_pend_abort_count_increment : forall processed priority,
  0 <= event_pend_abort_count processed < 255 ->
  event_pend_abort_count (processed ++ [priority]) = event_pend_abort_count processed + 1.
Proof.
  intros processed priority Hbound.
  rewrite event_pend_abort_count_snoc, Byte.add_unsigned, Byte.unsigned_one.
  assert (Hrepr : Byte.unsigned (Byte.repr (event_pend_abort_count processed)) =
    event_pend_abort_count processed).
  { apply Byte.unsigned_repr; change (0 <= event_pend_abort_count processed <= 255); lia. }
  rewrite Hrepr; apply Byte.unsigned_repr;
    change (0 <= event_pend_abort_count processed + 1 <= 255); lia.
Qed.

(** The following preservation principle is restricted to this API's
    literal ABORT steps. It transports source facts, never spatial cells. *)
Lemma q_pend_abort_broadcast_preserves : forall (P : UCOS2_Verify_State -> Prop) sg eid,
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node ->
    node.(eventType) = OS_EVENT_TYPE_Q ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendQ 0 PendAbort)) ->
  forall before priorities after,
    event_broadcast sg eid PendQ 0 PendAbort before priorities after ->
    forall node, UCOS2_state_inv sg before -> q_post_lookup before eid node ->
      node.(eventType) = OS_EVENT_TYPE_Q -> P before -> P after.
Proof.
  intros P sg eid Hpreserve before priorities after Hloop.
  induction Hloop as [state node Hnode Hzero|state node priority middle priorities after Hnode Hgroup Hcall Hloop IH];
    intros initial Hvalid Hinitial Htype HP; [exact HP|].
  assert (node = initial) by congruence; subst node.
  destruct (event_wake_decompose sg state eid initial PendQ 0 PendAbort priority middle
    Hvalid Hinitial ltac:(rewrite Htype; reflexivity) Hgroup Hcall)
    as [tid [tail [old [Hlist [Hold [Hpriority [Hmiddle [Hmiddle_valid Hmiddle_node]]]]]]]].
  eapply IH; [exact Hmiddle_valid|exact Hmiddle_node|exact Htype|].
  rewrite Hmiddle; eapply Hpreserve; eassumption.
Qed.

Lemma q_pend_abort_critical_preserves : forall (P : UCOS2_Verify_State -> Prop) sg eid,
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node ->
    node.(eventType) = OS_EVENT_TYPE_Q ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendQ 0 PendAbort)) ->
  forall before node opt result after,
    UCOS2_state_inv sg before -> q_post_lookup before eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
    q_pend_abort_critical sg eid opt before result after -> P before -> P after.
Proof.
  intros P sg eid Hpreserve before node opt result after Hvalid Hnode Htype [other [Hother Hstep]] HP.
  assert (other = node) by congruence; subst other.
  destruct (Z.eqb (encode_event_wait_grp node.(waitList) before.(TskState)) 0) eqn:Hgroup.
  - destruct Hstep as [_ ->]; exact HP.
  - apply Z.eqb_neq in Hgroup; destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [Hloop _]].
      eapply q_pend_abort_broadcast_preserves; eassumption.
    + destruct Hstep as [priority [Hcall _]].
      destruct (event_wake_decompose sg before eid node PendQ 0 PendAbort priority after
        Hvalid Hnode ltac:(rewrite Htype; reflexivity) Hgroup Hcall)
        as [tid [tail [old [Hlist [Hold [Hpriority [-> Hrest]]]]]]].
      eapply Hpreserve; eassumption.
Qed.

Lemma q_pend_abort_wake_preserves_ready_nonempty : forall sg state eid node tid old,
  state.(SchedState).(readyList) <> [] ->
  (event_wake_state sg state eid node tid old PendQ 0 PendAbort).(SchedState).(readyList) <> [].
Proof.
  intros sg state eid node tid old Hready.
  destruct state.(SchedState).(readyList) as [|slot tail] eqn:Hlist; [contradiction|].
  assert (Hmember : In slot
    (event_wake_state sg state eid node tid old PendQ 0 PendAbort).(SchedState).(readyList)).
  { apply (proj2 (sched_wake_by_status_membership _ _ _ _ _ _)); left; rewrite Hlist; left; reflexivity. }
  intro Hempty; rewrite Hempty in Hmember; contradiction.
Qed.

Lemma q_pend_abort_wake_preserves_disabled_source : forall sg state eid node tid old view,
  sched_disabled_entry_source view state ->
  sched_disabled_entry_source view (event_wake_state sg state eid node tid old PendQ 0 PendAbort).
Proof.
  intros sg state eid node tid old view Hsource.
  unfold sched_disabled_entry_source, sched_disabled_isr_source in *.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS IntrState SchedState].
  rewrite sched_wake_by_status_running_eq; exact Hsource.
Qed.

Lemma q_pend_abort_wake_preserves_task_source : forall sg state eid node tid old call,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_resume_caller_source sg (ResumeTaskCaller call) state ->
  task_resume_caller_source sg (ResumeTaskCaller call)
    (event_wake_state sg state eid node tid old PendQ 0 PendAbort).
Proof.
  intros sg state eid node tid old call Hold [[Horigin [Hactive Hcurrent]] [Havailable Haddress]].
  assert (Hcur : (event_wake_state sg state eid node tid old PendQ 0 PendAbort).(SchedState).(curTaskID) =
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

Lemma q_pend_abort_prefix_wake_decompose : forall environment critical sg original mask pe eid opt before
  observed returned restored count error,
  UCOS2_state_inv sg before -> q_post_call_input critical sg original pe before eid observed ->
  q_pend_abort_prefix_program environment critical sg original mask pe eid opt before
    (((count, error), true), returned) restored ->
  exists active saved acquired node released code,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    q_post_acquire_facts environment critical sg original active mask saved before acquired eid observed node /\
    q_pend_abort_critical sg eid (unsigned_last_nbits opt 8) acquired (count, (code, true)) released /\
    UCOS2_state_inv sg released /\
    task_resume_restore_program environment critical sg active released returned restored.
Proof.
  intros environment critical sg original mask pe eid opt before observed returned restored count error
    Hvalid Hinput Hprefix.
  unfold q_pend_abort_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype.
  destruct Hprefix as [active [saved [acquired [number [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]]].
  injection Hresult as Hnumber Hcode Hschedule Hcaller; subst number schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  destruct (q_post_acquire_identity environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype Hfacts) as [node Hacquire].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hg]]]]].
  pose proof (proj1 (event_pend_abort_critical_preserves_resources sg acquired eid node PendQ
    (unsigned_last_nbits opt 8) (count, (code, true)) released (proj1 Hfacts) Hnode
    ltac:(rewrite Hqueue; reflexivity) Hstep)) as Hreleased.
  exists active, saved, acquired, node, released, code.
  split; [exact Hfacts|]; split; [exact Hacquire|]; auto.
Qed.

Lemma q_pend_abort_schedule_protocol_task : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  before.(SchedState).(readyList) <> [] ->
  q_pend_abort_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored count error Hprefix.
  destruct (q_pend_abort_prefix_wake_decompose environment critical sg (ResumeTaskCaller call)
    mask pe eid opt before observed returned restored count error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  assert (Hreleased_source : task_resume_caller_source sg (ResumeTaskCaller active) released).
  { eapply (q_pend_abort_critical_preserves
      (task_resume_caller_source sg (ResumeTaskCaller active)) sg eid).
    - intros; eapply q_pend_abort_wake_preserves_task_source; eassumption.
    - exact Hacquired.
    - exact Hnode.
    - exact Hqueue.
    - exact Hstep.
    - exact Hactive. }
  destruct (q_post_task_restore_source environment critical sg active returned released restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hreleased_ready : released.(SchedState).(readyList) <> []).
  { eapply (q_pend_abort_critical_preserves
      (fun state => state.(SchedState).(readyList) <> []) sg eid).
    - intros; apply q_pend_abort_wake_preserves_ready_nonempty; assumption.
    - exact Hacquired.
    - exact Hnode.
    - exact Hqueue.
    - exact Hstep.
    - exact Hacquired_ready. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma q_pend_abort_schedule_protocol_task_idle : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  task_idle_ready sg before.(TskState) ->
  q_pend_abort_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients Hreturns Hsource Hidle.
  eapply q_pend_abort_schedule_protocol_task;
    [exact Hvalid|exact Hinput|exact Hclients|exact Hreturns|exact Hsource|].
  eapply sched_idle_ready_nonempty;
    [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle].
Qed.

Lemma q_pend_abort_schedule_protocol_disabled : forall environment critical sg view mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  q_pend_abort_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid opt before.
Proof.
  intros environment critical sg view mask pe eid opt before observed Hvalid Hinput Hclients Hsource
    returned restored count error Hprefix.
  destruct (q_pend_abort_prefix_wake_decompose environment critical sg (ResumeGenericCaller view)
    mask pe eid opt before observed returned restored count error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  assert (Hreleased_source : sched_disabled_entry_source view released).
  { eapply (q_pend_abort_critical_preserves (sched_disabled_entry_source view) sg eid).
    - intros; apply q_pend_abort_wake_preserves_disabled_source; assumption.
    - exact Hacquired.
    - exact Hnode.
    - exact Hqueue.
    - exact Hstep.
    - exact Hacquired_source. }
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    released restored Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma q_pend_abort_schedule_protocol_null : forall environment critical sg caller mask eid opt before,
  q_pend_abort_schedule_protocol environment critical sg caller mask 0 eid opt before.
Proof.
  intros environment critical sg caller mask eid opt before returned restored count error Hprefix.
  unfold q_pend_abort_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma q_pend_abort_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_pend_abort_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hpe Htype returned restored count error Hprefix.
  unfold q_pend_abort_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

(** Boot is admitted by its initializer and registered history, not by an
    origin tag.  No scheduling-return fact is required on the no-wait path. *)
Lemma q_pend_abort_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> q_post_call_input critical sg caller pe before eid observed ->
  (forall active saved acquired node,
    q_post_save_facts environment critical sg caller active mask saved before acquired ->
    q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed node ->
    node.(waitList) = []) ->
  q_pend_abort_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hempty
    returned restored count error Hprefix.
  destruct (q_pend_abort_prefix_wake_decompose environment critical sg caller mask pe eid opt before
    observed returned restored count error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  pose proof (Hempty active saved acquired node Hsave Hacquire) as Hnil.
  destruct Hstep as [actual [Hactual Hstep]].
  assert (actual = node) by congruence; subst actual.
  rewrite Hnil in Hstep; cbn [encode_event_wait_grp Z.eqb] in Hstep.
  destruct Hstep as [Hresult _]; discriminate.
Qed.

Lemma q_pend_abort_schedule_protocol_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> q_post_call_input critical sg caller pe before eid observed ->
  q_post_queues_no_waiters before -> q_post_no_waiters_clients critical ->
  q_pend_abort_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hempty Hclients.
  eapply q_pend_abort_schedule_protocol_acquired_no_waiters; [exact Hvalid|exact Hinput|].
  intros active saved acquired node Hfacts Hacquire.
  destruct Hfacts as [Hacquired [Hinterval Hrest]].
  destruct Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  destruct (q_post_interval_preserves_no_waiters critical sg
    (task_resume_view caller).(os_execution_invocation) before acquired
    Hclients Hvalid Hempty Hinterval) as [_ Hempty_acquired].
  exact (Hempty_acquired eid node Hnode Hqueue).
Qed.

Lemma q_pend_abort_schedule_protocol_boot_sources : forall environment critical sg caller mask pe eid opt before observed
  task_name flag_name memory_name names invocation,
  UCOS2_state_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) ->
  critical_region_interval critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before ->
  q_post_call_input critical sg caller pe before eid observed ->
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  q_pend_abort_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed task_name flag_name memory_name names
    invocation Hboot Hhistory Hinput Hfamily.
  pose proof (q_post_no_waiters_clients_from_source_family critical Hfamily) as Hclients.
  destruct (q_post_interval_preserves_no_waiters critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before Hclients Hboot
    (q_post_boot_queues_no_waiters sg task_name flag_name memory_name names) Hhistory) as [Hvalid Hempty].
  eapply q_pend_abort_schedule_protocol_no_waiters; eassumption.
Qed.

Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.

Lemma q_pend_abort_boot_initializer_schedule_protocol : forall environment critical sg caller mask pe eid opt before observed
  task_name flag_name memory_name names invocation,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true -> sg.(osKernelConfig).(cfgMemoryNames) = true ->
    exists chars, readable_name names memory_name chars) ->
  critical_region_interval critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before ->
  q_post_call_input critical sg caller pe before eid observed ->
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names |--
  coq_prop (q_pend_abort_schedule_protocol environment critical sg caller mask pe eid opt before) &&
    UCOS2_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros environment critical sg caller mask pe eid opt before observed task_name flag_name memory_name names
    invocation Hprofile Htcb Hnames Hmemory Hhistory Hinput Hfamily.
  sep_apply_l_atomic (q_post_boot_initializer_establishes_no_waiters
    sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  Intros.
  pose proof (q_pend_abort_schedule_protocol_boot_sources environment critical sg caller mask pe eid opt before observed
    task_name flag_name memory_name names invocation (proj1 H) Hhistory Hinput Hfamily) as Hprotocol.
  entailer!.
Qed.
